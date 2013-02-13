"""
2010.9.1 CKS
A solution for the mind-switching problem exemplified in
http://en.wikipedia.org/wiki/The_Prisoner_of_Benda
http://theinfosphere.org/The_Prisoner_of_Benda

-todo:estimate the total number of remaining swaps, and abort if not enough?
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
        
    def test_mindswap(self):
        """
        Constructs and plans in a deterministic domain where an alien device
        has swapped the mind's of several people, and the planner is tasked
        with returning everyone's mind to their original body.
        
        http://en.wikipedia.org/wiki/The_Prisoner_of_Benda
        """
        
        domain = Domain(name='mindswap')
        self.assertTrue(domain.module)
        
        # Define operator.
        op_swap = Operator(
            name='swap',
            parameters=['?mind1','?body1','?mind2','?body2'],
            conditions=[
                ['?problem','swapcount','?count'],
                
                ['?problem','mindbody','?mb1'],
                ['?mb1','mind','?mind1'],
                ['?mb1','body','?body1'],
                
                ['?problem','mindbody','?mb2'],
                ['?mb2','mind','?mind2'],
                ['?mb2','body','?body2'],
                
                ['test', ['neq','?mind1','?mind2']],
                ['test', ['neq','?body1','?body2']],
                
                #TODO:convert expressions to OAVs?
#                se("""
#                (not (and
#                (?problem swapped ?swap2)
#                (?swap2 mind1 ?mind1)
#                (?swap2 body1 ?body2)
#                (?swap2 mind2 ?mind2)
#                (?swap2 body2 ?body1)
#                ))"""),
#                
#                se("(not (?problem swapped ?swap3))"),
#                se("(not (?swap3 mind1 ?mind2))"),
#                se("(not (?swap3 body1 ?body2))"),
#                se("(not (?swap3 mind2 ?mind1))"),
#                se("(not (?swap3 body2 ?body1))"),
#                
#                se("(not (?problem swapped ?swap4))"),
#                se("(not (?swap4 mind1 ?mind2))"),
#                se("(not (?swap4 body1 ?body1))"),
#                se("(not (?swap4 mind2 ?mind1))"),
#                se("(not (?swap4 body2 ?body2))"),
            ],
            effects=[
                ['branch'],
                se("(del (?problem swapcount ?count))"),
                se("(add (?problem swapcount (+ ?count 1)))"),
                se("(del (?problem mindbody ?mb1))"),
                se("(del (?mb1 mind ?mind1))"),
                se("(del (?mb1 body ?body1))"),
                se("(del (?problem mindbody ?mb2))"),
                se("(del (?mb2 mind ?mind2))"),
                se("(del (?mb2 body ?body2))"),
                se("(add (?problem swapped ?swap=uuid))"),
                se("(add (?swap mind1 ?mind1))"),
                se("(add (?swap body1 ?body1))"),
                se("(add (?swap mind2 ?mind2))"),
                se("(add (?swap body2 ?body2))"),
                se("(add (?problem mindbody ?mbA=uuid))"),
                se("(add (?mbA mind ?mind1))"),
                se("(add (?mbA body ?body2))"),
                se("(add (?problem mindbody ?mbB=uuid))"),
                se("(add (?mbA mind ?mind2))"),
                se("(add (?mbA body ?body1))"),
            ])
        pprint(str2sexpr(op_swap._clips_lhs_cleanppform()), indent=4)
        domain.add_operator(op_swap)
#        self.assertEqual(op_swap._var_names,
#            set(['count', 'swap4', 'swap2', 'swap3', 'mind1', 'mind2', 'body1',
#                 'problem', 'body2', 'mb1', 'mb2']))
#        self.assertEqual(op_swap._func_names, set(['uuid']))
        
        domain.fitness = Fitness(conditions=[
                ['?problem','swapcount','?count'],
            ],
            expr="fitness(?_state, int(?count))")
        
        swapcount = Fact(o='_', a='swapcount', v=0)
        facts0 = [swapcount]
        env = Environment(facts0, domain=domain)
        s_a = env.state
        
        import yaml
        domain_yml = yaml.dump({'domain':domain}, indent=4, width=80)#, default_flow_style=0)
        open('domains/mindswap/domain.yml','w').write(domain_yml)
        
    def test_planning(self):
        
        fn1 = 'domains/mindswap/domain.yml'
        fn2 = 'domains/mindswap/domain2.yml'
        domain = Domain.load(fn1)
        self.assertEqual(domain.name, 'mindswap')
        domain.save(fn2)
        self.assertEqual(open(fn1).read(), open(fn2).read())
        
        
        import uuid
        facts = Fact.from_sexpr("""
        (entity (name Professor) (mind Professor-mind) (body Professor-body))
        (entity (name Zoidberg) (mind Zoidberg-mind) (body Zoidberg-body))
        (entity (name Ethan-Bubblegum-Tate) (mind Ethan-Bubblegum-Tate-mind) (body Ethan-Bubblegum-Tate-body))
        (entity (name Sweet-Clyde) (mind Sweet-Clyde-mind) (body Sweet-Clyde-body))
        """, functions={'uuid':lambda:str(uuid.uuid4())})
        for f in facts:
            print fact
        
#        planner = Planner(facts0, domain, min_sample_size=50, debug=1)
#        planner.debug = True
#        self.assertEqual(planner.pending, True)
#        self.assertEqual(len(planner._state_heap), 1)
#        self.assertEqual(len(planner._states), 1)
#        
#        plan_iter = planner.plan()
#        plan_iter.next()
        
if __name__ == '__main__':
    unittest.main()