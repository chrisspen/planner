"""
2010.9.1 CKS
A solution for the mind-switching problem exemplified in
http://en.wikipedia.org/wiki/The_Prisoner_of_Benda
http://theinfosphere.org/The_Prisoner_of_Benda

-todo:estimate the total number of remaining swaps, and abort if not enough?
"""
from __future__ import print_function, absolute_import

import os
import sys
import unittest

from ..sexpr import se
from .. import planner as p
from ..planner import Collector, Environment

TEST_DIR = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, TEST_DIR)

class Test(unittest.TestCase):

    def setUp(self):
        # Clear instance caches.
        p.State.STATES.clear()
        p.Fact.FACTS.clear()
        p.Domain.DOMAINS.clear()

    def test_mindswap(self):
        """
        Constructs and plans in a deterministic domain where an alien device
        has swapped the mind's of several people, and the planner is tasked
        with returning everyone's mind to their original body.

        http://en.wikipedia.org/wiki/The_Prisoner_of_Benda
        """

        domain = p.Domain(name='mindswap')
        self.assertTrue(domain.module)

        # Define operator.
        op_swap = p.Operator(
            name='swap',
            parameters=['?mind1', '?body1', '?mind2', '?body2'],
            conditions=[
                ['?problem', 'swapcount', '?count'],

                ['?problem', 'mindbody', '?mb1'],
                ['?mb1', 'mind', '?mind1'],
                ['?mb1', 'body', '?body1'],

                ['?problem', 'mindbody', '?mb2'],
                ['?mb2', 'mind', '?mind2'],
                ['?mb2', 'body', '?body2'],

                ['test', ['neq', '?mind1', '?mind2']],
                ['test', ['neq', '?body1', '?body2']],

                se("""(not (and
                    (?problem swapped ?swap2)
                    (?swap2 mind1 ?mind1)
                    (?swap2 body1 ?body2)
                    (?swap2 mind2 ?mind2)
                    (?swap2 body2 ?body1)
                ))"""),

                se("""(not (and
                    (?problem swapped ?swap1)
                    (?swap1 mind1 ?mind1)
                    (?swap1 body1 ?body1)
                    (?swap1 mind2 ?mind2)
                    (?swap1 body2 ?body2)
                ))"""),
#
                se("""(not (and
                    (?problem swapped ?swap3)
                    (?swap3 mind1 ?mind2)
                    (?swap3 body1 ?body2)
                    (?swap3 mind2 ?mind1)
                    (?swap3 body2 ?body1)
                ))"""),
#
                se("""(not (and
                    (?problem swapped ?swap4)
                    (?swap4 mind1 ?mind2)
                    (?swap4 body1 ?body1)
                    (?swap4 mind2 ?mind1)
                    (?swap4 body2 ?body2)
                ))"""),
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
                se("(add (?mbB mind ?mind2))"),
                se("(add (?mbB body ?body1))"),
            ])
        #pprint(str2sexpr(op_swap._clips_lhs_cleanppform()), indent=4)
        domain.add_operator(op_swap)
#        self.assertEqual(op_swap._var_names,
#            set(['count', 'swap4', 'swap2', 'swap3', 'mind1', 'mind2', 'body1',
#                 'problem', 'body2', 'mb1', 'mb2']))
#        self.assertEqual(op_swap._func_names, set(['uuid']))

        domain.fitness = p.Fitness(conditions=[
                ['?problem', 'swapcount', '?count'],
            ],
            collectors=[
                Collector(
                    'mind-body-matches',
                    [
                        se("(?problem entity ?e)"),
                        se("(?e mind ?mind)"),
                        se("(?e body ?body)"),
                        se("(?problem mindbody ?mb)"),
                        se("(?mb mind ?mind)"),
                        se("(?mb body ?body)"),
                    ]
                )
            ],
            expression="fitness(?env, ?problem, ?count)")

        swapcount = p.Fact(o='_', a='swapcount', v=0)
        facts0 = [swapcount]
        env = Environment(facts0, domain=domain)
        s_a = env.state

        import yaml
        domain_yml = yaml.dump({'domain':domain}, indent=4, width=80)#, default_flow_style=0)
        open(os.path.join(TEST_DIR, 'domains/mindswap/domain.yml'), 'w').write(domain_yml)

    def test_planning(self):

        fn1 = os.path.join(TEST_DIR, 'domains/mindswap/domain.yml')
        fn2 = os.path.join(TEST_DIR, 'domains/mindswap/domain2.yml')
        domain = p.Domain.load(fn1)
        self.assertEqual(domain.name, 'mindswap')
        self.assertTrue(domain.module)
        domain.save(fn2)
        self.assertEqual(open(fn1).read(), open(fn2).read())

        import uuid
        facts0 = list(p.Fact.from_sexpr(
            open(os.path.join(TEST_DIR, 'domains/mindswap/problem-new.txt'), 'r').read(),
            functions={'uuid': lambda: str(uuid.uuid4())}))

        planner = p.Planner(
            facts=facts0,
            domain=domain,
            estimator=p.AlwaysHopeful(),
            min_sample_size=50,
            debug=1)
        planner.iter_type = p.ITER_PER_STATE
        #planner.iter_type = p.ITER_PER_ACTION

        self.assertEqual(len(planner.env.facts), len(facts0))
        self.assertEqual(len(planner.env.state.facts), len(facts0))
        self.assertEqual(planner.debug, True)
        self.assertEqual(planner.pending, True)
        self.assertEqual(len(planner._state_heap), 1)
        self.assertEqual(len(planner._states), 1)

        plan_iter = planner.plan()
        steps = 0
        try:
            while 1:
                steps += 1
                plan_iter.next()
                if not steps % 10:
                    print('states evaluated:', planner._state_count)
                    print('states pending:', planner.size)
                    print('best fitness:', planner.best_fitness)
                    print('best plan:', planner.get_best_plan())
        except StopIteration:
            pass
        best_plan = planner.get_best_plan()
        print('final best plan:', best_plan)

        self.assertEqual(planner.size, 0)
        self.assertEqual(planner.pending, False)

if __name__ == '__main__':
    unittest.main()
