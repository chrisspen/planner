"""
2011.12.21 CKS
An A* based automated planner.
"""
import os, sys
import copy
from pprint import pprint
from StringIO import StringIO
import heapq
import re
import cPickle as pickle
import hashlib
from collections import defaultdict
from heapq import heappush, heappop
import yaml
try:
    from collections import OrderedDict
except ImportError:
    from ordereddict import OrderedDict
    
_hash = hash

import clips
from sexpr import str2sexpr, sexpr2str

FITNESS_RULE = "fitness_rule"
LABELER_RULE = "labeler_rule"
BRANCH = 'branch'
CHANGE = 'change'
OR = 'or'
RESERVED_CLIPS_SYMBOLS = (
    'test', 'not', 'and', OR, 'neq', 'eq', 'oav',
)

def tupleit(t):
    """
    Recursively transforms all nested lists into equivalent nested tuples.
    """
    return tuple(map(tupleit, t)) if isinstance(t, (list, tuple)) else t

def sortit(t, key=None):
    """
    Recursively sorts all nested sequence-type objects.
    """
    if callable(key):
        t = key(t)
    if isinstance(t, dict):
        return sorted((sortit(k),sortit(v)) for k,v in t.iteritems())
    if isinstance(t, (list, tuple, set, frozenset)):
        return sorted(sortit(_) for _ in t)
    return t

def hashit(t, key=None):
    """
    Creates a platform-independent hash for an arbitrary nesting of sequence
    types.
    """
    t = list(sortit(t, key=key))
    t = pickle.dumps(t)
    h = hashlib.sha512(t)
    return h.digest()

class LiteralMismatch(Exception):
    pass

class ORMismatch(Exception):
    pass

def get_variable_values(a, b, d=None, depth=0):
    """
    Walks two nested list structures, and finds the values corresponding to
    variable names in one of the structures.
    """
    if d is None:
        d = {}
#    print '    '*depth,'getvar_a:',
#    pprint(a, indent=4)
#    print '    '*depth,'getvar_b:',
#    pprint(b, indent=4)
    if isinstance(a, basestring) and isinstance(b, basestring):
        if a.startswith('?') and b.startswith('?'):
            raise Exception, "Variables can't match other variables: %s %s" % (a, b)
        elif a.startswith('?'):
            a_name = a[1:].strip()
            a_value = b
            if a_name in d:
                assert d[a_name] == a_value
            elif a_name:
                d[a_name] = a_value
        elif b.startswith('?'):
            b_name = b[1:].strip()
            b_value = a
            if b_name in d:
                assert d[b_name] == b_value
            elif b_name:
                d[b_name] = b_value
        elif a != b:
            raise LiteralMismatch
    elif isinstance(a, (tuple,list)) and isinstance(b, (tuple,list)):
        if a and b and a[0] == OR and b[0] == OR:
            raise Exception, "Matching across simultaneous OR expressions " \
                + "is not supported."
        if a and b and ((a[0] == OR and b[0] != OR) or (a[0] != OR and b[0] == OR)):
            # Match a literal expression to a list of ORed patterns.
            # Returns the bindings associated with the first pattern that
            # matches the literal expression.
            if a[0] == OR:
                or_list = a[1:]
                other_list = b
            else:
                or_list = b[1:]
                other_list = a
            found = False
            for _i,or_part in enumerate(or_list):
                #print '    '*depth,'or_part:',_i,or_part
                # Find the first OR part that matches.
                try:
                    for av,bv in zip(other_list,or_part):
                        get_variable_values(av, bv, d, depth=depth+1)
                    found = True
                    break
                except LiteralMismatch:
                    pass
            if not found:
                raise ORMismatch, ("No matches to the OR " +
                    "expression found: %s") % (str(or_list),)
        else:
            for av,bv in zip(a,b):
                get_variable_values(av, bv, d, depth=depth+1)
    else:
        raise Exception, "Type mistmatch: %s != %s" % (type(a),type(b))
    return d

def _get_clips_output(obj, method):
    """
    Captures the output of PyClips objects that print directly to stdout.
    """
    from StringIO import StringIO
    _stdout = sys.stdout
    try:
        sys.stdout = StringIO()
        getattr(obj, method)()
        return sys.stdout.getvalue()
    finally:
        sys.stdout = _stdout

def _get_clips_match_sets(s, env, fact_index, rule_lhs_index):
    import re
    from sexpr import str2sexpr
    matches = re.findall("(?P<ruleid>[a-zA-Z0-9\-_]+)\:\s+(?P<facts>(?:,?f-[0-9]+)+)", s)
    rule_matches = {} # {ruleid:[[facts],[facts]}
    #print 'matches:',matches
    for ruleid,factlist in matches:
        _factlist = factlist
        factlist = []
        for f in _factlist.split(','):
            fi = int(f.split('-')[1])
            ppform = fact_index[fi].CleanPPForm()
            v = str2sexpr(ppform)[0]
            factlist.append(v)
        lhs_patterns = [
            pattern for pattern in str2sexpr(rule_lhs_index[ruleid])
            if pattern[0] != 'test' and pattern[0] != 'not']
        var_dict = get_variable_values(factlist, lhs_patterns)
        rule_matches.setdefault(ruleid, list())
        rule_matches[ruleid].append(var_dict)
        assert len(factlist) == len(lhs_patterns), "There is a mismatch " \
            + "between the number of facts matching the left-hand side, " \
            + "and the number of fact patterns in the left-hand side."
    return rule_matches

def walk_tree(lst, cb):
    """
    Recursively walks the nested sequence structure, calling the given callable
    on non-sequence elements.
    Assumes a directed non-cyclic structure.
    Otherwise, infinite looping will occur.
    """
    assert callable(cb)
    if isinstance(lst, (tuple, list)):
        for el in lst:
            walk_tree(el, cb)
    else:
        cb(lst)

def walk_tree_and_replace(lst, d):
    """
    Recursively walks a nested list structure and replaces strings with values
    defined in the given dictionary.
    Replaces list elements in-place.
    """
    assert isinstance(lst, list)
    assert isinstance(d, dict)
    new_lst = []
    for el in lst:
        if isinstance(el, list):
            new_lst.append(walk_tree_and_replace(el, d))
        else:
            new_lst.append(d.get(el, el))
    return new_lst

class Operator(object):
    """
    Represents an object that transforms the state.
    """
    def __init__(self, name, conditions, effects, parameters=None, command=None):
        self.domain = None
        self.name = name
        self.parameters = parameters
        self.conditions = conditions
        self.command = command
        self.effects = effects
        self._var_names = None
        self._func_names = set()
        self._kwargs = {}
        
        self._update_var_names()
        self._check_effects()
    
    @classmethod
    def load_from_dict(cls, d):
        o = cls(**d)
        return o
    
    def __unicode__(self):
        return "<%s %s>" % (type(self).__name__, self.name)
    
    def __repr__(self):
        return unicode(self)
    
    def __cmp__(self, other):
        if not isinstance(other, Operator):
            return NotImplemented
        return cmp((self.name, self.conditions, self.effects),
                   (self.name, other.conditions, other.effects))
    
    def _clips_lhs_cleanppform(self):
        """
        Converts the left-hand-side pattern into the equivalent Clips
        s-expression syntax.
        Attempts to auto-convert the implied (o a v) pattern into the
        equivalent Clips template.
        """
        c = []
        for condition in self.conditions:
            #TODO:recursively traverse pattern and auto-convert all 3-length
            #facts that don't begin with a reserved symbol to OAV?
            #TODO:expand list of reserved symbols in Clips
            if len(condition) == 3 \
            and condition[0] not in RESERVED_CLIPS_SYMBOLS:
                c.append(['oav'] + map(list, zip(['o','a','v'], condition)))
            else:
                c.append(condition)
        return sexpr2str(c)
    
    @property
    def domain(self):
        return getattr(self, '_domain', None)
    
    @domain.setter
    def domain(self, domain):
        self._domain = domain
        if self.domain and self.domain.module:
            for func_name in self._func_names:
                if not hasattr(self.domain.module, func_name):
                    raise Exception, "Unknown function name: %s" % (func_name,)
                elif not callable(getattr(self.domain.module, func_name)):
                    raise Exception, "Function not callable: %s" % (func_name,)
    
    def _update_var_names(self):
        self._var_names = set()
        def add_var_name(el):
            el = str(el)
            if not el.startswith('?') or len(el) <= 1:
                return
            if el[1].isdigit() or el[1] == '_':
                raise Exception, "Invalid variable name: %s" % (el[1:],)
            self._var_names.add(el[1:].strip())
        walk_tree(self.conditions, add_var_name)
    
    def _check_effects(self):
        """
        Recursively walks the effects structure, and ensures all names are
        correctly bound.
        """
        func_name_pattern = re.compile("([a-zA-Z][a-zA-Z0-9_]*)\(")
        local_names = set() # a set of variable names defined locally
        def cb(el):
            el = str(el)
            if el.startswith('for '):
                left,right = el.split(' in ')
                local_names.update(re.findall("\?([a-zA-Z][a-zA-Z0-9_]*)", left))
                other_names = re.findall("\?([a-zA-Z][a-zA-Z0-9_]*)", right)
#                print 'local_names:',local_names
#                print 'other_names:',other_names
                for other_name in other_names:
                    assert other_name in local_names \
                    or other_name in self._var_names, ("Unknown name in " +
                        "effects for statement: %s") % (other_name,)
                #self._func_names.update(re.findall("([a-zA-Z][a-zA-Z0-9_]*)\(", right))
                self._func_names.update(func_name_pattern.findall(right))
            elif el.startswith('?'):
                #name = el[1:].strip()
                matches = re.findall("\?([a-zA-Z][a-zA-Z0-9_]*)(?:=([a-zA-Z]+))?", el)
                if matches:
                    name,definer = matches[0]
                    if definer:
                        # A definer present means this name is being set for
                        # the first time, so confirm no similar name has
                        # already been defined.
                        assert name not in local_names
                        local_names.add(name)
                        self._func_names.add(definer)
                        #TODO:confirm definer exists?
                        #TODO:register name with definer so branch will auto-call definer?
                    else:
                        assert name in local_names or name in self._var_names,\
                            "Unknown name in effects: %s" % (name,)
        walk_tree(self.effects, cb)
    
    def __getstate__(self):
        d = OrderedDict()
        d['name'] = self.name
        d['parameters'] = self.parameters
        d['conditions'] = self.conditions
        d['effects'] = self.effects
        return d
    
    def __iter__(self):
        return self.__getstate__().iteritems()

    def _make_func(self, expr):
        assert isinstance(expr, basestring)
        
        def _get(n):
            return self._kwargs.get(n)
        
        BUILTINS = dict((t.__name__,t) for t in [int,float,bool])
        
        funcnames = re.findall("(?<!\?)([a-zA-Z_][a-zA-Z0-9_]*)\(", expr)
        func_bindings = {'_get':_get}
        for funcname in funcnames:
            if hasattr(self.domain.module, funcname):
                func_bindings[funcname] = getattr(self.domain.module, funcname)
            elif funcname in locals():
                func_bindings[funcname] = locals()[funcname]
            elif funcname in globals():
                func_bindings[funcname] = globals()[funcname]
            elif funcname in BUILTINS:
                func_bindings[funcname] = BUILTINS[funcname]
            else:
                raise Exception, "Unknown function: %s" % (funcname,)
        
        varnames = re.findall("\?[a-zA-Z_][a-zA-Z0-9_]*", expr)
        for varname in varnames:
            #self._varnames.add(varname[1:])
            expr = expr.replace(varname, "_get('%s')" % varname[1:])
        return eval("lambda: %s" % expr, func_bindings)

    def _get_action(self, local_kwargs):
        result = walk_tree_and_replace(self.parameters, local_kwargs)
        return "%s(%s)" % (self.name, ','.join(result,))

    def _eval_rhs(self, **kwargs):
        """
        Given a dictionary of keyword arguments matching the left-hand-side,
        iterates over all derived branches, returning a tuple of the form
        (action, [facts]).
        """
        
        pending = defaultdict(list) # {action:[facts]}
        action_name = None
        action_name0 = None
        self._kwargs = kwargs
        for effect in self.effects:
            
            rest = [effect]
            #print 'effect:',effect
            for_vars = [] # list of names
            for_func = lambda:[[]] # iterates over sets of name values
            if effect and isinstance(effect[0], basestring) \
            and effect[0].startswith('for '):
                for_expr, rest = effect
                for_vars_str,for_func_str = for_expr[4:].split(' in ')
                for_vars = re.findall("(\?[a-zA-Z][a-zA-Z0-9_]*)",for_vars_str)
                for_func = self._make_func(for_func_str)
                
            for ret in for_func():
                local_kwargs = dict(zip(for_vars, ret)+[('?'+k,v)
                                    for k,v in kwargs.iteritems()])
                action_name0 = action_name
                action_name = self._get_action(local_kwargs)
                
                # If the action changes, and we have pending facts, then yield
                # the facts for the last action.
                if action_name0 and action_name0 != action_name \
                and pending[action_name0]:
#                    if kwargs.get('curpos') == 'd':
#                        print 'a:',kwargs
#                        print 'action_name0:',action_name0
#                        print 'action_name1:',action_name
                    yield action_name0, pending[action_name0]
                    pending[action_name0] = []
                
                for sexpr in rest:
                    if sexpr[0] == BRANCH:
                        # If a new branch is found, then immeidately yield the
                        # current set of facts.
                        if pending[action_name]:
#                            if kwargs.get('curpos') == 'd':
#                                print 'b:',kwargs
#                                print 'action_name0:',action_name0
#                                print 'action_name1:',action_name
                            yield action_name, pending[action_name]
                            pending[action_name] = []
                    else:
                        sexpr = walk_tree_and_replace(sexpr, local_kwargs)
                        if sexpr[0] == CHANGE:
                            sexpr[1] = [
                                (str(clips.Eval(sexpr2str(el)))
                                    if isinstance(el,list) else el)
                                for el in sexpr[1]
                            ]
                            assert len(sexpr[1]) == 3
                            fact = Fact(**dict(zip(('o','a','v'), sexpr[1])))
                            pending[action_name].append(fact)
                        else:
                            raise Exception, "Expression not supported: %s" \
                                % (sexpr[0],)
        
        # Yield any remaining facts for the last action.
        if pending[action_name]:
#            if kwargs.get('curpos') == 'd':
#                print 'c:',kwargs
#                print 'action_name0:',action_name0
#                print 'action_name1:',action_name
            yield action_name, pending[action_name]
            pending[action_name] = []

def validate_goal_fitness(lst):
    if not lst:
        return
    assert len(lst) == 2

class Fitness(object):
    """
    Represents a generic function that can collect arguments from left-hand
    side rule pattern.
    """
    def __init__(self, conditions, expression, domain=None):
        self.domain = domain
        self.conditions = conditions
        self.expression = expression
        self._varnames = set()
        self._func = None
        self._kwargs = {}
    
    @classmethod
    def load_from_dict(cls, d):
        f = cls(**d)
        return f
    
    def _clips_lhs_cleanppform(self):
        c = []
        for condition in self.conditions:
            if len(condition) == 3:
                c.append(['oav'] + map(list, zip(['o','a','v'], condition)))
            else:
                c.append(condition)
        return sexpr2str(c)
    
    def _make_func(self, expr):
        assert isinstance(expr, basestring)
        
        def _get(n):
            return self._kwargs.get(n)
        
        BUILTINS = dict((t.__name__,t) for t in [int,float,bool])
        
        funcnames = re.findall("(?<!\?)([a-zA-Z_][a-zA-Z0-9_]*)\(", expr)
        func_bindings = {
            '_get':_get,
            'kwargs':self._kwargs,
        }
        for funcname in funcnames:
            if hasattr(self.domain.module, funcname):
                func_bindings[funcname] = getattr(self.domain.module, funcname)
            elif funcname in locals():
                func_bindings[funcname] = locals()[funcname]
            elif funcname in globals():
                func_bindings[funcname] = globals()[funcname]
            elif funcname in BUILTINS:
                func_bindings[funcname] = BUILTINS[funcname]
            else:
                raise Exception, "Unknown function: %s" % (funcname,)
        
        varnames = re.findall("\?[a-zA-Z_][a-zA-Z0-9_]*", expr)
        for varname in varnames:
            self._varnames.add(varname[1:])
            expr = expr.replace(varname, "_get('%s')" % varname[1:])
        return eval("lambda: %s" % expr, func_bindings)
    
    @property
    def func(self):
        if self._func is None and self.expression:
            self.func = self.expression
        return getattr(self, '_func', None)
    
    @func.setter
    def func(self, expr):
        self.expression = expr
        self._func = self._make_func(expr)

    def __getstate__(self):
        d = OrderedDict()
        d['conditions'] = sorted(c for c in (self.conditions or []))
        d['expression'] = self.expression
        return d
    
    def __iter__(self):
        return self.__getstate__().iteritems()
    
    def __call__(self, **kwargs):
        self._kwargs.clear()
        self._kwargs.update(kwargs)
        missing = set(self._varnames).difference(self._kwargs.keys())
        assert not missing, \
            "The parameters %s were not provided." \
            % (', '.join("'%s'" % n for n in sorted(missing)),)
        return self.func()

LABEL_EXPECTED_FITNESS_DEFAULT = 'expected_fitness_default'
LABEL_EXPECTED_FITNESS_AGGREGATOR = 'expected_fitness_aggregator'
LABELS = set([
    LABEL_EXPECTED_FITNESS_DEFAULT,
    LABEL_EXPECTED_FITNESS_AGGREGATOR,
])

class Labeler(Fitness):
    """
    Represents a rule that applies labels to a state based on the state's
    facts.
    """
    def __init__(self, labels, **kwargs):
        super(Labeler, self).__init__(**kwargs)
        for label in labels:
            assert label in LABELS, 'Unknown label: %s' % (label,)
        self.labels = set(labels)
        
    def __call__(self, **kwargs):
        result = super(Labeler, self).__call__(**kwargs)
        assert isinstance(result, dict)
        labels = set(result.iterkeys())
        assert labels == self.labels, "Mismatched labels: %s" % (labels,)
        return result

class Domain(object):
    """
    Represents a collection of transition rules and a state fitness heuristic.
    """
    
    DOMAINS = {}
    
    def __init__(self, **kargs):
        self.module = None
        self.name = kargs.get('name')
        self.operators = set()
        self.format = 1

    def __cmp__(self, other):
        if not isinstance(other, Domain):
            return NotImplemented
        return cmp(
            (self.module, self.name, self.operators),
            (other.module, other.name, other.operators)
        )

    def __getstate__(self):
        d = OrderedDict()
        d['name'] = self.name
        d['format'] = self.format
        d['operators'] = sorted(o for o in self.operators)
        d['fitness'] = self.fitness
        return d

    @property
    def fitness(self):
        return getattr(self, '_fitness', None)
    
    @fitness.setter
    def fitness(self, o):
        if isinstance(o, Fitness):
            o.domain = self
            self._fitness = o
        else:
            self._fitness = Fitness(o, domain=self)

    @property
    def labeler(self):
        return getattr(self, '_labeler', None)
    
    @labeler.setter
    def labeler(self, o):
        if not isinstance(o, Labeler):
            return NotImplemented
        o.domain = self
        self._labeler = o

    @property
    def name(self):
        return getattr(self, '_name', None)
        
    @name.setter
    def name(self, name):
        if name:
            assert name not in self.DOMAINS, \
                ("Domain '%s' is already registered. Unregistered the " +
                "existing domain or use a unique name for the current " +
                "domain.") % name
            self.DOMAINS[name] = self
        elif self.name in self.DOMAINS:
            del self.DOMAINS[self.name]
        self._name = name
        
        self.module = None
        if name:
            try:
                self.module = getattr(__import__('domains.%s' % name), name)
            except ImportError:
                raise

    def add_operator(self, op, force=False):
        """
        Adds an operator to the state and creates an equivalent
        rule in the internal Clips environment.
        """
        assert isinstance(op, Operator)
        if not force:
            assert op not in self.operators, \
                "Operator %s has already been added." % (op,)
        self.operators.add(op)
        op.domain = self
    
    @classmethod
    def load_from_dict(cls, d):
        #pprint(d,indent=4)
        assert 'domain' in d, "Structure is not a domain description."
        parts = d['domain']
        d = cls()
        for el_type, value in parts.iteritems():
            if el_type == 'name':
                d.name = value.strip()
            elif el_type == 'format':
                d.format = int(value)
            elif el_type == 'operators':
                for op_data in value:
                    d.add_operator(Operator.load_from_dict(op_data))
            elif el_type == 'fitness':
                d.fitness = Fitness.load_from_dict(value)
            else:
                raise Exception, 'Unknown domain element: %s' % (el_type,)
        return d
    
    @classmethod
    def loads(cls, s):
        expr = str2sexpr(s)
        expr = expr[0]
        assert expr[0] == 'domain', "Expression is not a domain description."
        d = cls()
        for el in expr[1:]:
            el_type = el[0]
            if el_type == 'name':
                d.name = el[1]
            elif el_type == 'operator':
                d.add_operator(Operator(el))
            elif el_type == 'fitness':
                assert len(el[1:]) == 2, \
                    "Malformed goal-fitness. Should be two parts."
                d.fitness = el[1:]
                #validate_goal_fitness(d.fitness)
        #assert p.goal_fitness, 'Problem is missing it\'s goal fitness.'
        return d
        
    @classmethod
    def load(cls, fn):
        if fn.endswith('.yml') or fn.endswith('.yaml'):
            return cls.load_from_dict(yaml.load(open(fn, 'r')))
        return cls.loads(open(fn,'r').read())
    
    def save(self, fn):
        if isinstance(fn, basestring):
            fn = open(fn, 'w')
        fn.write(yaml.dump({'domain':self}, indent=4, width=80))

def dump_anydict_as_map(anydict):
    yaml.add_representer(anydict, _represent_dictorder)
    
def _represent_dictorder(self, data):
    if isinstance(data, (Domain)):
        return self.represent_mapping('tag:yaml.org,2002:map',
                                      data.__getstate__().items(), 0)
    elif isinstance(data, (Operator)):
        return self.represent_mapping('tag:yaml.org,2002:map', data, 0)
    elif isinstance(data, (Fitness)):
        return self.represent_mapping('tag:yaml.org,2002:map', data, 0)
    else:
        return self.represent_mapping('tag:yaml.org,2002:map', data.items())

dump_anydict_as_map(Domain)
dump_anydict_as_map(Operator)
dump_anydict_as_map(Fitness)

def _get_fact_data(*args, **kwargs):
    if args:
        assert len(args) == 3, "If specified, there must be exactly 3 fact arguments."
    data = dict(zip('oav', args))
    data.update(kwargs)
    return data

class Fact(object):
    """
    An immutable globally unique object containing a set of key/value pairs.
    """
    
    FACTS = {} # {hash:Fact}
    
    def __new__(cls, *args, **kwargs):
        data = _get_fact_data(*args, **kwargs)
        hash = hashit((str(k),str(v)) for k,v in data.iteritems())
        if hash in cls.FACTS:
            return cls.FACTS[hash]
        fact = super(Fact, cls).__new__(cls)
        cls.FACTS[hash] = fact
        fact.hash = hash
        fact.data = dict((str(k),str(v)) for k,v in data.iteritems())
        return fact
    
    def __init__(self, *args, **kwargs):
        data = _get_fact_data(*args, **kwargs)
        d = self.__dict__
        if 'data' not in d:
            self.data = dict((str(k),str(v)) for k,v in data.iteritems())
        if 'hash' not in d:
            self.hash = hashit(self.data)
        if '_clips_fact' not in d:
            self._clips_fact = None

    @classmethod
    def from_sexpr(cls, facts_str, functions=None, var_map=None):
        """
        A helper function for creating facts from a string containing fact
        s-expressions, with optionally embedded Python functions.
        
        Assumes the facts are formatted like "(object attribute subject)".
        """
        functions = functions or {}
        facts_list = str2sexpr(facts_str)
        if var_map is None:
            var_map = {} # {name:value}
        var_map.clear()
        for i, fact_list in enumerate(facts_list):
            assert len(fact_list) == 3, ("Invalid fact \"%s\". Facts must " +
                "be triples and consist of three values, an object, "  +
                "attribute and value.") % (str(fact_list),)
            lst = []
            for j,v in enumerate(fact_list):
                if v.startswith('?'):
                    name = v[1:].strip()
                    func_name = None
                    if '=' in name:
                        name,func_name = name.split('=')
                    assert len(name), "Invalid name %s in fact %i." % (v, j,)
                    if func_name:
                        assert name not in var_map, ("Variable name \"%s\" " +
                            "was already defined.") % (name,)
                        assert func_name in functions, ("Unknown function " +
                            "\"%s\"") % (func_name,)
                        v = var_map[name] = functions[func_name]()
                    else:
                        assert name in var_map, ("Unknown variable name: %s") \
                            % (name,)
                        v = var_map[name]
                lst.append(v)
            yield Fact(**dict(zip('oav',lst)))

    def __getattr__(self, name):
        if name in self.data:
            return self.data.get(name)
        if hasattr(super(Fact, self), '__getattr__'):
            return super(Fact, self).__getattr__(name)
    
    def __hash__(self):
        return _hash(self.hash)
    
    def __cmp__(self, other):
        if not isinstance(other, type(self)):
            return NotImplemented
        #return cmp(self.hash, other.hash)
        return cmp(self._to_tuple(), other._to_tuple())
    
    def _to_tuple(self):
        return tuple(sorted(self.data.items()))
    
    def __unicode__(self):
        s = []
        if set(self.keys()) == set('oav'):
            s.extend("%s=%s" % (k, self.data[k]) for k in 'oav')
        else:
            for k in sorted(self.keys()):
                s.append("%s=%s" % (k, self.data[k]))
        s = ', '.join(s)
        return "<Fact: %s>" % s
    
    def __repr__(self):
        return unicode(self)
    
    def _clips_cleanppform(self):
        if set(self.data.keys()) == set(['o','a','v']):
            ppform = ['oav'] + map(list, self.data.items())
        else:
            ppform = map(list, self.data.items())
        return sexpr2str(ppform)
    
    def keys(self):
        return self.data.keys()
    
    def unique_key(self):
        if set(self.data.keys()) == set(['o','a','v']):
            return (('a',self.data['a']),('o',self.data['o']))
        return tuple(sorted(self.keys()))

F = Fact

class State(object):
    """
    Represents a single unique discrete collection of facts.
    
    Note, we don't store the actual facts in the state object, because this
    would entail a huge amount of redundancy and memory usage.
    
    It's assumed the state at time T0 shares most of its facts with the
    state at time T1, therefore it's easier to store the difference in facts
    between the states instead of the entire fact set of each state.
    
    Instead, a state only stores the hash of the frozenset of facts and the
    references to parent and child states. We store a differential record of
    fact additions and deletions in a separate model, which we reference to
    lookup the literal fact set.
    """
    STATES = {} # {hash:state} Global index of unique states.
    
    def __new__(cls, hash=None, facts=None):
        assert facts or hash, "Either facts or hash must be given."
        if facts:
            hash = hashit(f.data for f in sorted(facts))
            facts = None
        if hash in cls.STATES:
            return cls.STATES[hash]
        state = super(State, cls).__new__(cls)
        cls.STATES[hash] = state
        state.hash = hash
        return state
    
    def __init__(self, hash=None, facts=None):
        assert facts or hash, "Either facts or hash must be given."
        d = self.__dict__
        if 'parents' not in d:
            self.parents = set() # set([State])
        if 'children' not in d:
            self.children = set() # set([State])
        if 'hash' not in d:
            if facts:
                hash = hashit(f.data for f in sorted(facts))
            self.hash = hash
        if 'facts' not in d:
            self.facts = facts
        
        # {child_state:set([(action,dellist,addlist)])}
        if 'transitions' not in d:
            self.transitions = defaultdict(set)
    
    def __hash__(self):
        return _hash(self.hash)
    
    def __cmp__(self, other):
        if not isinstance(other, State):
            return NotImplemented
        return cmp(self.hash, other.hash)

    def __contains__(self, thing):
        if not isinstance(thing, Fact):
            return NotImplemented
        return thing in self.facts

    def find_facts(self, **kwargs):
        """
        Returns a list of facts matching the given key/value literals.
        Note, this assumes the state is explicitly storing all facts, which is
        only done in debugging mode.
        """
        matches = []
        if not self.facts:
            return matches
        for fact in self.facts:
            skip = False
            for k,v in kwargs.iteritems():
                if fact.data.get(k) != v:
                    skip = True
                    break
            if skip:
                continue
            matches.append(fact)
        return matches

    @staticmethod
    def find_shortest_path(end_node, start_node, neighbors):
        """
        Searches for the shortest path between two nodes in a state graph.
        
        Parameters:
        
            end_node := The state at the end of the path.
            start_node := The state at the start of the path.
            neighbors := A callable that takes a state and returns allowable
                states that can be transitioned to from the given a state.
        """
        #TODO:memoize?
        # [(total cost to get to node, path)]
        heap = [(0, (start_node,))]
        priors = set()
        while heap:
            
            # Get next node to evaluate.
            current = heappop(heap)
            current_cost,current_path = current
            current_node = current_path[-1]
            
            # Check for goal.
            if current_node == end_node:
                return current_path
            
            # Check for loops.
            if current_node in priors:
                continue
            priors.add(current_node)
            
            # Retrieve neighbors.
            for next_node in neighbors(current_node):
                if next_node in priors:
                    continue
                # Queue neighbor for evaluation.
                heappush(heap, (current_cost+1, current_path+(next_node,)))
                if next_node == end_node:
                    # Stop prematurely if we've found the goal.
                    break

    def add_child(self, action=None, addlist=None, dellist=None, state=None):
        """
        Links two states in a parent/child relationship.
        """
        assert isinstance(state, State)
        self.children.add(state)
        state.parents.add(self)
        if addlist is not None:
            addlist = frozenset(addlist)
        if dellist is not None:
            dellist = frozenset(dellist)
        self.transitions[state].add((action,dellist,addlist))
        
    def __getstate__(self):
        return dict(
            parents=self.parents,
            children=self.children,
            hash=self.hash,
            transitions=self.transitions)

class Environment(object):
    """
    Represents the current working environment of facts being evaluated.
    """
    
    def __init__(self, facts, domain=None):
        
        self.facts = set()
        self.key_to_fact = {} # {key:fact}
        self._env = None
        self.domain = domain
        self._set_facts(facts)
    
    def _set_facts(self, facts):
        """
        Sets the current state of the environment.
        This should only be used to setup the initial facts.
        For incremental updates, use update() so a proper
        state tree will be maintained.
        """
        if not facts:
            return
        for fact in facts:
            self.add_fact(fact)
        self._state = State(facts=self.facts)
    
    @property
    def activated_operators(self):
        match_sets = self.match_sets
        for ruleid in match_sets.iterkeys():
            if ruleid in (FITNESS_RULE, LABELER_RULE):
                continue
            yield self._rule_id_to_operator[ruleid]
    
    def add_fact(self, new_fact):
        """
        Indexes a fact in the environment.
        If a fact with the same keys currently exists in the environment,
        this existing fact will be unindexed and returned.
        Used internally.
        External fact additions should be done through update().
        """
        assert isinstance(new_fact, Fact)
        if new_fact in self.facts:
            return
        
        old_fact = self.key_to_fact.get(new_fact.unique_key())
        if old_fact:
            self.del_fact(old_fact)
            
        self.facts.add(new_fact)
        self.key_to_fact[new_fact.unique_key()] = new_fact
        
        if self._env:
            
            # Add the new fact to the Clips backend.
            ppform = new_fact._clips_cleanppform()
            f = new_fact._clips_fact = self._env.Assert(ppform)
            self._clips_fact_index[new_fact._clips_fact.Index] = f
        
        self._match_sets_clean = False
        return old_fact
        
    def add_rule(self, id, lhs, rhs=None):
        """
        Creates the rule in the environment.
        Used internally to register a domain's operator as a rule in the
        backend.
        """
        assert id not in self._clips_rule_lhs_index, \
            "There already exists a rule with ID %s." % (id,)
        #pprint(str2sexpr(lhs), indent=4)
        rule = self._env.BuildRule(id, lhs, "", "")
        self._clips_rule_lhs_index[id] = lhs
        self._match_sets_clean = False
        return rule
        
    def del_fact(self, old_fact):
        """
        Removes a fact from the environment.
        """
        assert isinstance(old_fact, Fact)
        if old_fact not in self.facts:
            return
        
        del self.key_to_fact[old_fact.unique_key()]
        self.facts.remove(old_fact)
        
        if self._env:
            
            # Remove the old fact from the Clips backend.
            if old_fact._clips_fact and old_fact._clips_fact.Index:
                old_fact_index = old_fact._clips_fact.Index
                if old_fact._clips_fact.Exists:
                    old_fact._clips_fact.Retract()
                if old_fact_index in self._clips_fact_index:
                    del self._clips_fact_index[old_fact_index]
                    
        self._match_sets_clean = False
    
    @property
    def domain(self):
        return getattr(self, '_domain', None)
    
    @domain.setter
    def domain(self, domain):
        self._domain = domain
        
        if self.domain:
            # Reset Clips backend.
            if self._env:
                self._env.Clear()
            else:
                self._env = clips.Environment()
            self._clips_fact_index = {} # {id:clips fact}
            self._clips_rule_lhs_index = {} # {ruleid:lhs}
            self._fact_to_clipsfact = {}
            self._rule_id_to_operator = {} # {ruleid:operator}
            self._env.Reset()
            self._env.BuildTemplate("oav", """
    (multislot o (default nil))
    (multislot a (default nil))
    (multislot v (default nil))""", '')
            
            self._state = None
            self._match_sets = {} # {ruleid:[{name:value},...]
            self._match_sets_clean = False
            self._clips_fitness_rule = None
            
            for operator in domain.operators:
                assert operator.name != FITNESS_RULE, \
                    "Rule id %s is reserved." % (FITNESS_RULE,)
                assert operator.name != LABELER_RULE, \
                    "Rule id %s is reserved." % (LABELER_RULE,)
                self._rule_id_to_operator[operator.name] = operator
                self.add_rule(
                    id=operator.name,
                    lhs=operator._clips_lhs_cleanppform()[1:-1])
            
            assert self.domain.fitness, "No fitness function has been set."
            lhs = self.domain.fitness._clips_lhs_cleanppform()[1:-1]
            self._clips_fitness_rule = self.add_rule(FITNESS_RULE, lhs)
            
            self._clips_labeler_rule = None
            if self.domain.labeler:
                lhs = self.domain.labeler._clips_lhs_cleanppform()[1:-1]
                self._clips_labeler_rule = self.add_rule(LABELER_RULE, lhs)
    
    def exists(self, thing):
        if isinstance(thing, Fact):
            return thing in self.facts
        return NotImplemented
    
    def fitness(self):
        """
        Returns the fitness of the current environment state,
        as defined by the domain's fitness equation.
        
        If there are multiple match sets for the fitness equation,
        this will separately evaluate each match set and return the minimum
        fitness value.
        """
        if not self.domain or not self._env:
            return
        fitness_matches = self.match_sets.get(FITNESS_RULE, [])
        best = -1e99999
        for match_set in fitness_matches:
            score = self.domain.fitness(**match_set)
            best = max(best, score)
        return best
    
    def get_facts(self, **kwargs):
        for f in self.facts:
            skip = False
            for k,v in kwargs.iteritems():
                if f.data.get(k) != v:
                    skip = True
                    break
            if skip:
                continue
            else:
                yield f
    
    def labels(self):
        """
        Returns a dictionary of key/value pairs to be applied to the current
        state.
        """
        if not self.domain or not self._env:
            return
        matches = self.match_sets.get(LABELER_RULE, [])
        labels = {}
        for match_set in matches:
            labels.update(self.domain.labeler(**match_set))
        return labels
    
    @property
    def match_sets(self):
        """
        Returns a dictionary containing each unique set of matches for the
        left-hand-side of each rule.
        
        Since we query this from the Clips backend by parsing the text-output
        of Clips's PrintAgenda function, we lazily extract this by tracking
        when our local cache becomes outdated by new fact or rule additions,
        and only re-parse when the match sets are requested.
        """
        if not self._match_sets_clean:
            out = _get_clips_output(self._env, 'PrintAgenda')
            self._match_sets = _get_clips_match_sets(
                out,
                self._env,
                self._clips_fact_index,
                self._clips_rule_lhs_index)
            self._match_sets_clean = True
        return self._match_sets
    
    def reset(self, facts=None):
        """
        Removes all facts from memory, but not rules.
        Note, set_facts() must be called to re-define the initial state.
        """
        self.facts.clear()
        self._fact_to_clipsfact.clear()
        self.key_to_fact.clear()
        self._clips_fact_index.clear()
        self._env.Reset()
        self._match_sets_clean = False
        self._state = None
        
        self._set_facts(facts)
        
    @property
    def state(self):
        """
        Returns the hashed state node in the state graph representing
        the current loaded fact set.
        """
        return self._state
    
    def switch(self, state):
        """
        Loads the facts associated with the given state.
        """
        
        path = State.find_shortest_path(
            end_node=state,
            start_node=self.state,
            neighbors=lambda s:s.children.union(s.parents),)
        #path = [current_state,...,goal_state]
        
        if not path:
            raise Exception, "Unable to switch to state."
        
        path = zip(path,path[1:])
        for from_state,to_state in path:
            
            # Retrieve the fact change lists.
            if to_state in from_state.transitions:
                # Traversing the state graph forward.
                transitions = from_state.transitions[to_state]
                action,dellist,addlist = list(transitions)[0]
            else:
                # Traversing the state graph in reverse, so we need to reverse
                # the add/delete lists.
                assert from_state in to_state.transitions
                transitions = to_state.transitions[from_state]
                action,addlist,dellist = list(transitions)[0]
                
            # Apply the change lists.
            #TODO:aggregate del/add lists and commit after iteration?
            if dellist:
                for fact in dellist:
                    self.del_fact(fact)
            if addlist:
                for fact in addlist:
                    self.add_fact(fact)
                    
            # Set the new current state.
            self._state = to_state
    
    def update(self, action, changelist):
        """
        Modifies the environment state.
        
        Parameters:
        
            action := An object representing the action that caused the change.
            
            changelist := A list of Facts that have changed.
        
        Returns the new state object created or retrieved.
        """
        
        # Commit fact changelist.
        dellist = []
        addlist = changelist
        for new_fact in changelist:
            old_fact = self.add_fact(new_fact)
            if old_fact:
                dellist.append(old_fact)
                
        # Hash new state.
        new_state = State(facts=self.facts)
        
        # Link state graph.
        self.state.add_child(
            action=action,
            addlist=addlist,
            dellist=dellist,
            state=new_state)
        
        # Set new state.
        self._state = new_state
        
        return new_state

import numpy as np
#from scipy.optimize import curve_fit

def linreg(X, Y):
    """
    Summary
        Linear regression of y = ax + b
    Usage
        Slope    Y-Int    R = linreg(list, list)
    Returns coefficients to the regression line "y=ax+b" from x[] and y[],
    and R^2 Value
    """
    if len(X) != len(Y):  raise ValueError, 'unequal length'
    N = len(X)
    Sx = Sy = Sxx = Syy = Sxy = 0.0
    for x, y in map(None, X, Y):
        Sx = Sx + x
        Sy = Sy + y
        Sxx = Sxx + x*x
        Syy = Syy + y*y
        Sxy = Sxy + x*y
    det = Sxx * N - Sx * Sx
    a, b = (Sxy * N - Sy * Sx)/det, (Sxx * Sy - Sx * Sxy)/det
    meanerror = residual = 0.0
    for x, y in map(None, X, Y):
        meanerror = meanerror + (y - Sy/N)**2
        residual = residual + (y - a * x - b)**2
    if not meanerror:
        return 0.0, 0.0, 0.0
    RR = 1 - residual/meanerror
    ss = residual / (N-2)
    Var_a, Var_b = ss * N / det, ss * Sxx / det
    return a, b, RR

def sigmoid(x, x0, k, a, c):#, d):
    y0 = 1 / (1 + np.exp(-k*(x-x0)))
    #y0 = (1 - y0)*(1 - d) + y0*d
    y = a * y0 + c
    return y

def calculate_r2(yi, fi):
    SSreg = sum((p0-p1)**2 for p0,p1 in zip(yi,fi))
    y_mean = sum(yi)/float(len(yi))
    SStot = sum((i-y_mean)**2 for i in yi)
    R2 = 1.0 - SSreg/SStot
    return R2

class Estimator(object):
    """
    Calculates the probability of a given event appearing in a sequence
    assuming a linear model.
    """
    def __init__(self, event, min_sample_size=100):
        self.event = event
        
        # The minimum number of samples given globally
        # before any estimates will be given.
        self.min_sample_size = min_sample_size
        
        # This determines how the probability associated with infrequently
        # sampled values are weighted.
        # A value of N means that the probability will be weighted by
        # min(S,N)/N, where S is the current number of samples.
        # A value of 1 means no weighting occurs.
        self.local_sample_size = 5
        
        self._counts = defaultdict(int)
        self._totals = defaultdict(int)
        self._sample_count = 0
        
        self._last = None
        self._clean = False
    
    def add(self, next):
        """
        Adds a sample to the estimator.
        """
        if self._last is not None:
            self._counts[self._last] += next == self.event
            self._totals[self._last] += 1
        self._last = next
        self._sample_count += 1
        self._clean = False
    
    def _get_prior(self, v):
        if not self._totals[v]:
            return
        dx = self._counts[v]
        dy = float(self._totals[v])
        rdx = min(self._totals[v], self.local_sample_size)
        rdy = float(self.local_sample_size)
        return (dx/dy)*(rdx/rdy)
    
    def __call__(self, v):
        """
        Returns the probability of the given value preceding the event.
        """
        if self._sample_count < self.min_sample_size:
            return
        
        if not self._clean:
            x = np.array(sorted(self._totals.keys()))
            y = np.array([self._get_prior(_x) for _x in x])
            
            if not len(y):
                return
            
            # Calculate linear regression.
            a,b,RR = linreg(x,y)
            
            # Record estimate for all known x values.
            xtest = np.array(sorted(set(self._totals.keys()+[v])))
            ylin = np.array(a*_x + b for _x in xtest)
            self._dlin = dict(zip(xtest,ylin.tolist()))
            
            #TODO:sigmoid? and use whichever has the higher r^2?
            
            self._clean = True
        
        return max(self._dlin[v], 0)

class Planner(object):
    """
    Represents an A* based search algorithm.
    """
    
    def __init__(self, facts, domain,
        min_sample_size=100,
        quit_threshold=0.01,
        debug=False):
        
        self._env = Environment(facts=facts, domain=domain)
        
        self.debug = debug
        
        # Stores states whose transitions need to be evaluated.
        self._state_heap = [] # [(fitness,state)]
        
        # Stores all states whose fitness has been evaluated.
        # This needs to be a heap so we can quickly find the best
        # states to formulate a complete plan.
        self._states = [] # [(fitness,state)]
        self._states_prior = set()
        self._state_fitness = {} # {state:fitness}
        self._state_expected_fitness = {} # {state:best fitness of children}
        self._state_expected_fitness_default = {}
        self._state_expected_fitness_agg = {}
        
        # Planning registers.
        # Current step in evaluating current state.
        self._i = None
        
        # Total number of steps for current state.
        self._i_total = None
        
        # Total number of states visited (may include duplicates).
        self._state_count  = None
        
        # The state of the "real" world, regardless of the simulated
        # environment or planning.
        # This will be used to guide the planner in "real-time"
        # and construct complete plans.
        self._current_state = self._env.state
        self._current_facts = list(self._env.facts)
        
#        self._best_plan = None
#        self._best_plan_clean = False
        
        # The best state fitness observed. Minimized.
        self._best_fitness = None
        
        # The number of evaluations since the last best fitness was found.
        self._i_since_best = 0
        
        # Estimation of whether or not the next evaluation will be the next
        # best fitness.
        self._continue_est = Estimator(
            event=0,
            min_sample_size=min_sample_size)
        self.quit_threshold = quit_threshold
        
        # Finally, queue the initial state for evaluation.
        self._push_state()
        
    def get_expected_fitness(self, state, default=None):
        """
        Returns the expected fitness for the state, as defined by the domain.
        """
        if state in self._state_expected_fitness:
            return self._state_expected_fitness[state]
        return default
        
    def _push_state(self):
        """
        Pushes the current environment state onto the heap.
        """
        self._continue_est.add(self._i_since_best)
        self._i_since_best += 1
        fitness = self._env.fitness()
        self.best_fitness = fitness
        state = self._env.state
        if self.debug:
            state.facts = list(self._env.facts)
        self._state_fitness[state] = fitness
        item = (fitness,state)
        heapq.heappush(self._state_heap, item)
        heapq.heappush(self._states, item)
        self._states_prior.add(state)
        
        # Record labels.
        labels = self._env.labels()
        if labels:
#            self._env.domain.module.print_board(state)
            for label,value in labels.iteritems():
                if label == LABEL_EXPECTED_FITNESS_DEFAULT:
                    self._state_expected_fitness_default[state] = value
                elif label == LABEL_EXPECTED_FITNESS_AGGREGATOR:
                    assert callable(value), ("Expected fitness aggregator " +
                        "\"%s\" is not callable.") % (value,)
                    self._state_expected_fitness_agg[state] = value
        
        # Propagate state fitness to ancestors.
        stack = set(state.parents)
        priors = set()
        ef_defaults = self._state_expected_fitness_default
        while stack:
            parent_state = stack.pop()
            if parent_state in priors:
                continue
            priors.add(parent_state)
            assert isinstance(parent_state, State)
            
            #TODO:remove
#            agg_type_max = parent_state.find_facts(o='game0', a='turn')[0].data['v'] == 'x'
#            show = parent_state.find_facts(o='game0', a='moves')[0].data['v'] == '3'
#            if show:
#                self._env.domain.module.print_board(parent_state)
#                print 'push facts:',sorted(parent_state.facts)
#                print 'agg_type_max:',agg_type_max
#                print 'parent fitness0:',self._state_expected_fitness.get(parent_state)
            
            # Set aggregation settings based on type.
#            if agg_type_max:
#                _old_ef_default = 0
#                _agg_func = max
#            else:
#                _old_ef_default = +1e999999
#                _agg_func = min
#                
            old_ef_default = ef_defaults.get(parent_state, 0)
            agg_func = self._state_expected_fitness_agg.get(parent_state, max)
#            if _agg_func != agg_func:
#                print 'agg mismatch:', _agg_func,agg_func
#                self._env.domain.module.print_board(parent_state)
#                sys.exit()
                
            # Record the parent's previous expected fitness.
            old_ef = self.get_expected_fitness(
                parent_state,
                old_ef_default)
            
            if parent_state.children:
                
                # Retrieve the expected fitness of all children.
                child_expected_fitnesses = []
                for c in parent_state.children:
                    f = self.get_expected_fitness(c, self._state_fitness.get(c))
                    if f is None:
                        continue
                    child_expected_fitnesses.append(f)
                if not child_expected_fitnesses:
                    continue
                    
                # Find the aggregate expected fitness.
                new_ef = agg_func(child_expected_fitnesses)
                self._state_expected_fitness[parent_state] = new_ef
                
                # If the fitness changed, the queue the state's ancestors for
                # re-evaluation.
                if new_ef != old_ef:
                    stack.update(parent_state.parents)
            
            #TODO:remove
#            if show:
#                print 'parent fitness1:',self._state_expected_fitness.get(parent_state)
    
    def _pop_state(self, state=None):
        """
        If a state is given, removes that state from the heap.
        Otherwise, removes and returns the next (fitness,state) at the top of
        the heap.
        """
        if state:
#            while 1:
#                heap_removals = [(f,s) for f,s in self._state_heap if state == s]
#                if heap_removals:
#                    for item in heap_removals:
#                        self._state_heap.remove(item)
#                else:
#                    break
            try:
                item = (self._state_fitness[state],state)
                self._state_heap.remove(item)
            except ValueError:
                pass
            except KeyError:
                pass
        else:
            return heapq.heappop(self._state_heap)
        
    @property
    def best_fitness(self):
        return self._best_fitness
    
    @best_fitness.setter
    def best_fitness(self, v):
        if self.best_fitness is None or v > self.best_fitness:
            if self._best_fitness is not None:
                self._i_since_best = 0
            self._best_fitness = v

    @property
    def improvement_probability(self):
        """
        Returns the likelyhood of finding a better fitness by evaluating one
        more state.
        """
        return self._continue_est(self._i_since_best)

    def _get_next_actions(self):
        for child_state in self._current_state.children:
            transitions = self._current_state.transitions[child_state]
            for action,dellist,addlist in transitions:
                yield action

    def get_best_actions(self, current_state=None, with_child=False):
        current_state = current_state or self._current_state
        best = (-1e99999,None)
        for child_state in current_state.children:
            expected_fitness = self._state_expected_fitness.get(
                child_state,
                self._state_fitness.get(child_state))
            best = max(best, (expected_fitness,child_state))
        best_fitness,best_child_state = best
        if best_child_state is None:
            return
        transitions = current_state.transitions[best_child_state]
        actions = [action for action,_,_ in transitions]
        if with_child:
            return actions,best_child_state
        return actions

    def get_best_plan(self):
        current_state = self._current_state
        best_fitness = self._state_expected_fitness.get(
            current_state,
            self._state_fitness[current_state])
        plan = []
        while self._state_fitness[current_state] != best_fitness:
            actions,current_state = self.get_best_actions(
                current_state,
                with_child=True)
            plan.append(copy.deepcopy(actions))
        if not plan:
            return
        return plan
    
    @property
    def ratio_complete(self):
        """
        Returns a ratio representing the progress in evaluating the current
        state.
        """
        if isinstance(self._i, (int, float)) \
        and isinstance(self._i_total, (int, float)) and self._i_total:
            return self._i/float(self._i_total)
    
    @property
    def hopeful(self):
        """
        Returns true if we should continue planning, because we think we'll
        find a better state.
        Returns false if we should stop planning, because we think we will not
        find a better state.
        """
        if not self.pending:
            # There can be no hope of improvement if there are no more states
            # to evaluate.
            return False
        imp_prob = self.improvement_probability
        if imp_prob is None:
            return True
        return imp_prob > self.quit_threshold
    
    @property
    def pending(self):
        """
        Returns true if there are pending states to evaluate.
        Returns false otherwise.
        """
        return bool(self._state_heap)
    
    def plan(self):
        """
        Iteratively generates a state tree.
        """
        self._state_count = 0
        while self.pending:
            
            # Get next state to evaluate.
            fitness,state = self._pop_state()
            self._env.switch(state)

            match_sets = copy.deepcopy(self._env.match_sets)
            ops = list(self._env.activated_operators)
            #print 'ops:',ops
            self._i = 0
            self._i_total = sum(len(match_sets[op.name]) for op in ops)
            
#            show = False
#            if Fact(o='_',a='curpos',v='d') in state:
#                print '-'*80
#                print 'state',sorted(state.facts)
#                show = True
#                print '='*80
                
            for op in ops:
                for match_set in match_sets[op.name]:
                    self._i += 1
                    #print 'i:',self._i,match_set
                    
                    for action,changelist in op._eval_rhs(**match_set):
#                        if show:print 'action:',action
                        #print 'changelist:',changelist
                            
                        # If our estimated likelyhood of improvement drops
                        # below a given threshold, then abort.
                        if self.pending and not self.hopeful:
                            # Re-queue the current state in-case we wish to
                            # re-start our planning.
                            self._env.switch(state)
                            self._push_state()
                            return
                        
                        self._env.update(
                            action=action,
                            changelist=changelist)
                        self._state_count += 1
        
                        # Add the current state to the heap for future
                        # evaluation.
                        if self._env.state not in self._states_prior:
                            self._push_state()
                        
                        # Revert back to previous state to try new.
                        self._env.switch(state)
                        if self.debug:
                            self._env.state.facts = list(self._env.facts)
            
                        yield

    def update(self, action, state):
        """
        Changes the planner's model of the "real world" to the given state
        and updates planning structures.
        
        The "real world" state tells the planner where to start planning from.
        Any queued hypothetical states that it can't reach from the
        "real world" will be removed from the queue.
        
        Assumes that the given action was performed in the current state, which
        resulted in the given state.
        """
        
        # Get fact change list.
        assert state.facts
        before = {}
        after = {}
        for f in self._current_facts:
            before[f.unique_key()] = f.data.get('v')
        for f in state.facts:
            after[f.unique_key()] = f.data.get('v')
        changelist = [f for f in state.facts
            if after.get(f.unique_key()) != before.get(f.unique_key())]
        #TODO:handle fact deletions implied by missing facts?
        
        # Change current state.
        prior_current_state = self._current_state
        self._env.update(
            action=action,
            changelist=changelist)
        self._current_state = self._env.state
        self._current_facts = list(self._env.facts)
        
        # Find unreachable states in the heap.
        alive = defaultdict(set) # {state:set(living parents)}
        dead = set()
        queue = [prior_current_state] # [state,...]
        priors = set()
        while queue:
            # Get next state.
            next_state = queue.pop(0)
            if next_state in priors:
                continue
            priors.add(next_state)
            
            # Prune if all parents are dead.
            if next_state != self._current_state and not alive[next_state] \
            and next_state not in dead:
                dead.add(next_state)
                self._pop_state(next_state)
            
            # Queue children.
            for child_state in next_state.children:
                queue.append(child_state)
                alive[child_state] = set(p for p in child_state.parents
                                          if p not in dead)
                
        # Prune unreachable states in the heap.
        check = True
        while check:
            check = False
            for state in list(alive.keys()):
                if state == self._current_state:
                    continue
                elif alive[state]:
                    for parent in list(alive[state]):
                        if parent in dead:
                            # Recheck all other states in case others also
                            # depended on this dead parent.
                            check = True
                            alive[state].remove(parent)
                elif state not in dead:
                    # A state with no living parents is dead,
                    # so remove it from the heap.
                    del alive[state]
                    dead.add(state)
                    self._pop_state(state)
                    