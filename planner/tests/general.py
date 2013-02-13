"""
"""
import os
import sys
import unittest
import copy
from pprint import pprint

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from sexpr import str2sexpr, se

import planner
from planner import Planner, Domain, Environment, State, Fact, Fitness, \
    Operator, Estimator, sortit, Labeler

#sys.path.insert(0, 'domains/driving')
#import driving

class Test(unittest.TestCase):
    
    def setUp(self):
        # Clear instance caches.
        State.STATES.clear()
        Fact.FACTS.clear()
    
    def test_sortit(self):
        a = frozenset([frozenset([1,2,3]),frozenset(['a','b','c']),frozenset([0,(99,999,9999,123),'c'])]);
        self.assertEqual(planner.sortit(a),
                         [[0, [99, 123, 999, 9999], 'c'], [1, 2, 3], ['a', 'b', 'c']])
        a = [dict(abc=123,xyz='def'), (4,2,1)]
        self.assertEqual(planner.sortit(a),
                         [[1, 2, 4], [('abc', 123), ('xyz', 'def')]])
    
    def test_get_variable_values(self):
        facts = [['cat-name', 'mittens'], ['cat-has', 'mittens', 'paws']]
        pattern = [['cat-name', '?name'], ['cat-has', '?name', '?thing']]
        d = planner.get_variable_values(pattern, facts)
        self.assertEqual(d, dict(name='mittens', thing='paws'))
    
    def test_clips(self):
        import clips
        env = clips.Environment()
        env.Reset()
        
        rule_lhs_index = {}
        
        r1_lhs = "(duck ?name)"
        r1 = env.BuildRule("duck-rule",
            r1_lhs,
            "",
            "The Duck rule")
        rule_lhs_index[r1.Name] = r1_lhs
        
        r2_lhs = "(cat-name ?name)(cat-has ?name ?thing)"
        r2 = env.BuildRule("cat-rule",
            r2_lhs,
            "",
            "The Cat rule")
        rule_lhs_index[r2.Name] = r2_lhs
        
        fact_index = {}
        
        f1 = env.Assert("(duck daffy)")
        fact_index[f1.Index] = f1
        self.assertEqual(f1.Index, 1)
        
        f2 = env.Assert("(duck waldo)")
        fact_index[f2.Index] = f2
        self.assertEqual(f2.Index, 2)
        
        f3 = env.Assert("(cat-name mittens)")
        fact_index[f3.Index] = f3
        self.assertEqual(f3.Index, 3)
        
        f4 = env.Assert("(cat-has mittens paws)")
        fact_index[f4.Index] = f4
        
        out = planner._get_clips_output(env, 'PrintAgenda')
        match_sets = planner._get_clips_match_sets(out, env, fact_index, rule_lhs_index)
        d = {'duck-rule': [{'name': 'waldo'}, {'name': 'daffy'}],
             'cat-rule': [{'thing': 'paws', 'name': 'mittens'}]}
        self.assertEqual(match_sets, d)
    
    def test_fact(self):
        curpos = Fact(o='_', a='curpos', v='a')
        curpos2 = Fact(o='_', a='curpos', v='a')
        self.assertEqual(curpos, curpos2)
        self.assertEqual(id(curpos), id(curpos2))
        
        curtime = Fact(o='_', a='curtime', v='0')
        self.assertNotEqual(curpos, curtime)
        self.assertNotEqual(id(curpos), id(curtime))
        
        goalpos = Fact(o='_', a='goalpos', v='p')
        facts = [curpos, curtime, goalpos]
        self.assertEqual(curtime.v, '0')
        self.assertEqual(set(curtime.keys()), set(['a','o','v']))
    
    def _test_state(self):
        
        curpos = Fact(curpos='a')
        curtime = Fact(curtime=0)
        goalpos = Fact(goalpos='p')
        
        facts0 = [curpos,curtime,goalpos]
        env = Environment(facts0)
        
        s_a = env.state
        s_a_facts = set(env.facts)
        s_a2 = State(facts=facts0)
        self.assertEqual(s_a, s_a2)
        self.assertEqual(id(s_a), id(s_a2))
        
        # drive to a->b
        s_ab = env.update(action='drive(a,b)', changelist=[Fact(curpos='b'),Fact(curtime=5)])
        s_ab_facts = set(env.facts)
        self.assertEqual(len(State.STATES), 2)
        self.assertEqual(len(s_ab.parents), 1)
        self.assertEqual(len(s_ab.children), 0)
        self.assertTrue(s_ab not in s_ab.children)
        self.assertTrue(s_ab not in s_ab.parents)
        
        # drive to a->b->c
        s_abc = env.update(action='drive(b,c)', changelist=[Fact(curpos='c'),Fact(curtime=5+6)])
        self.assertEqual(len(State.STATES), 3)
        self.assertEqual(len(s_ab.parents), 1)
        self.assertEqual(len(s_ab.children), 1)
        self.assertTrue(s_ab not in s_ab.children)
        self.assertTrue(s_ab not in s_ab.parents)
        
        # revert back to a->b
        env.switch(s_ab)
        self.assertEqual(env.facts, set([Fact(curpos='b'),Fact(curtime=5),Fact(goalpos='p')]))
        self.assertEqual(env.facts, s_ab_facts)
        self.assertEqual(env.state, s_ab)
        
        # drive to a->b->d
        s_abd = env.update(action='drive(b,d)', changelist=[Fact(curpos='d'),Fact(curtime=5+10)])
        self.assertEqual(env.facts, set([Fact(curpos='d'),Fact(curtime=5+10),Fact(goalpos='p')]))
        self.assertEqual(len(s_ab.children), 2)

        # drive to a->b->c->l
        env.switch(s_abc)
        self.assertEqual(len(s_abc.children), 0)
        s_abcl = env.update(action='drive(c,l)', changelist=[Fact(curpos='l'),Fact(curtime=5+10+30)])
        self.assertEqual(env.facts, set([Fact(curpos='l'),Fact(curtime=5+10+30),Fact(goalpos='p')]))
        self.assertEqual(len(s_abc.children), 1)
        s_abcl_facts = set(env.facts)

        # drive to a->b->d->f
        env.switch(s_abd)
        s_abdf = env.update(action='drive(d,f)', changelist=[Fact(curpos='f'),Fact(curtime=5+10+5)])
        self.assertEqual(env.facts, set([Fact(curpos='f'),Fact(curtime=5+10+5),Fact(goalpos='p')]))

        # drive to a->b->d->g
        env.switch(s_abd)
        s_abdg = env.update(action='drive(d,g)', changelist=[Fact(curpos='g'),Fact(curtime=5+10+10)])
        self.assertEqual(env.facts, set([Fact(curpos='g'),Fact(curtime=5+10+10),Fact(goalpos='p')]))

        # drive to a->b->d->e
        env.switch(s_abd)
        self.assertEqual(len(s_abd.children), 2)
        s_abde = env.update(action='drive(d,e)', changelist=[Fact(curpos='e'),Fact(curtime=5+10+12)])
        self.assertEqual(env.facts, set([Fact(curpos='e'),Fact(curtime=5+10+12),Fact(goalpos='p')]))
        self.assertEqual(len(s_abd.children), 3)
        self.assertEqual(len(s_abde.parents), 1)

        self.assertEqual(len(State.STATES), 8)
        
        env.switch(s_a)
        self.assertEqual(env.facts, s_a_facts)
        env.switch(s_abcl)
        self.assertEqual(env.facts, s_abcl_facts)
    
    def test_estimator(self):
        # The 0 indicates the step at which we receive a reward, reseting the count.
        steps = [0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
                 0, 1, 2, 3, 4, 0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 0, 1, 2, 0,
                 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 1, 2, 3, 4,
                 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 1, 2]
        # Calculate probability of next step being 0.
        e = Estimator(event=0, min_sample_size=10)
        i = 0
        for step in steps:
            e.add(step)
            print step,e(step)
        for step in sorted(e._totals.keys()):
            est = e(step)
            if est is None:
                continue
            print "e(%s) = %.2f %i %i %.2f" % (step, est, e._counts[step], e._totals[step], e._get_prior(step))
    
if __name__ == '__main__':
    unittest.main()