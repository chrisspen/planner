from __future__ import print_function, absolute_import

import os
import sys
import unittest

from ..planner import Planner, Domain, Environment, State, Fact, Fitness, Operator

TEST_DIR = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, TEST_DIR)

class Test(unittest.TestCase):

    def setUp(self):
        # Clear instance caches.
        State.STATES.clear()
        Fact.FACTS.clear()

    def _test_driving(self):
        """
        Constructs and plans in a deterministic driving domain, mimicking the
        functionality of a GPS car navigator.
        """

#        domain = Domain.load('domains/driving/domain.txt')
#        self.assertEqual(len(domain.operators), 1)
#        self.assertEqual(domain.name, 'driving')
#        self.assertEqual(domain.DOMAINS.keys(), ['driving'])
#
        domain = Domain(name='driving')
        self.assertTrue(domain.module)

        # Define operator.
        op_drive_to = Operator(
            name='drive_to',
            parameters=['?nextpos'],
            conditions=[
                ['?a', 'curpos', '?curpos'],
                ['?a', 'goalpos', '?goalpos'],
                ['?a', 'curtime', '?curtime'],
                ['test', ['neq', '?curpos', '?goalpos']],
            ],
            effects=[
                ["for ?nextpos,?traveltime in iter_neighbors(?curpos)", [
                    ['branch'],
                    ['change', ['?a', 'curpos', '?nextpos']],
                    ['change', ['?a', 'curtime', ['+', '?curtime', '?traveltime']]],
                ]]
            ])
        domain.add_operator(op_drive_to)
        self.assertEqual(op_drive_to._var_names, set(['a', 'curtime', 'goalpos', 'curpos']))
        self.assertEqual(op_drive_to._func_names, set(['iter_neighbors']))
        #return

        # Define fitness function.
        #best=0 => 0 dist in 0 time
        #worse=1 => +inf dist in +inf
        domain.fitness = Fitness(conditions=[
#                ['oav', ['o', '?1'], ['a', 'curpos'], ['v', '?from']],
#                ['oav', ['o', '?1'], ['a', 'goalpos'], ['v', '?goalpos']],
#                ['oav', ['o', '?1'], ['a', 'curtime'], ['v', '?initialtime']],
                ['?a', 'curpos', '?curpos'],
                ['?a', 'goalpos', '?goalpos'],
                ['?a', 'curtime', '?curtime'],
            ],
            expression="1-(sig(dist(?curpos, ?goalpos))/2 + sig(float(?curtime)/100)/2)")

        self.assertEqual(domain.module.sig(-1000), -1)
        self.assertEqual(domain.module.sig(0), 0)
        self.assertEqual(domain.module.sig(+1000), 1)

        self.assertEqual(domain.fitness(curpos='p', goalpos='p', curtime=0), 1.0)
        self.assertEqual(domain.fitness(curpos='a', goalpos='p', curtime=0), 0.5)
        self.assertAlmostEqual(domain.fitness(curpos='a', goalpos='p', curtime=1000), 0.0, 1)

        curpos = Fact(o='_', a='curpos', v='a')
        curtime = Fact(o='_', a='curtime', v=1000)
        goalpos = Fact(o='_', a='goalpos', v='p')
        facts0 = [curpos, curtime, goalpos]
        env = Environment(facts0, domain=domain)
        s_a = env.state

        self.assertAlmostEqual(env.fitness(), 0.0, 1)

        s_p = env.update(
            action='drive(a,p)',
            changelist=[
                Fact(o='_', a='curpos', v='p'),
                Fact(o='_', a='curtime', v=0)
            ])
        for fact in env.facts:
            print('fact:', fact, fact._clips_cleanppform())
        self.assertEqual(len(env.facts), 3)
        self.assertEqual(env._match_sets_clean, False)
        self.assertEqual(env.fitness(), 1.0)
        self.assertEqual(env._match_sets_clean, True)

        s_p = env.update(
            action='drive(p,a)',
            changelist=[
                Fact(o='_', a='curpos', v='a'),
                Fact(o='_', a='curtime', v=1)
            ])
        self.assertEqual(len(env.facts), 3)
        self.assertEqual(env._match_sets_clean, False)
        self.assertAlmostEqual(env.fitness(), 0.50, 2)
        self.assertEqual(env._match_sets_clean, True)

        s_p = env.update(
            action='drive(a,p)',
            changelist=[
                Fact(o='_', a='curpos', v='p'),
                Fact(o='_', a='curtime', v=1000)
            ])
        self.assertEqual(len(env.facts), 3)
        self.assertEqual(env._match_sets_clean, False)
        self.assertAlmostEqual(env.fitness(), 0.5, 2)
        self.assertEqual(env._match_sets_clean, True)

        env.reset()
        self.assertEqual(len(env.facts), 0)

        facts = [
            Fact(o='_', a='curpos', v='a'),
            Fact(o='_', a='curtime', v=0),
            Fact(o='_', a='goalpos', v='p'),
        ]
        env.reset(facts)
        self.assertEqual(len(env.facts), 3)

        #env._env.PrintAgenda()
        match_sets = env.match_sets
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        op = ops[0]
        s0 = env.state
        for match_set in match_sets[op.name]:
            for action, changelist in op._eval_rhs(**match_set):
                _s = env.update(action=action, changelist=changelist)

                # Revert back to earilier state to try new.
                env.switch(s0)

        facts0 = [
            Fact(o='_', a='curpos', v='a'),
            Fact(o='_', a='curtime', v=0),
            Fact(o='_', a='goalpos', v='p'),
        ]

        planner = Planner(facts0, domain, min_sample_size=50, debug=1)
        planner.debug = True
        self.assertEqual(planner.pending, True)
        self.assertEqual(len(planner._state_heap), 1)
        self.assertEqual(len(planner._states), 1)

        print('Starting planner...')
        plan_iter = planner.plan()
        plan_iter.next()

        # Since the start of the example map has one connection and one
        # operator, the initial state should be completed in the first
        # iteration.
        self.assertEqual(planner.ratio_complete, 1.0)
        self.assertEqual(planner.pending, True)
        self.assertEqual(len(planner._state_heap), 1)
        self.assertEqual(len(planner._states_prior), 2)

        plan_iter.next()

        self.assertEqual(planner.ratio_complete, 1.0)
        self.assertEqual(planner.pending, True)
        self.assertEqual(len(planner._state_heap), 1)
        self.assertEqual(len(planner._states_prior), 3)

        f_curpos_b = Fact(o='_', a='curpos', v='b')
        #self.assertTrue()

        s_b0 = None
        try:
            for _ in range(1000):
                plan_iter.next()
        except StopIteration:
            pass
        self.assertEqual(len(planner._states_prior), 47)

        s_f = State(facts=[
            Fact(o='_', a='curpos', v='f'),
            Fact(o='_', a='curtime', v=20),
            Fact(o='_', a='goalpos', v='p'),
        ])
        self.assertEqual(len(s_f.transitions), 1)

        s_d = State(facts=[
            Fact(o='_', a='curpos', v='d'),
            Fact(o='_', a='curtime', v=15),
            Fact(o='_', a='goalpos', v='p'),
        ])
        self.assertEqual(len(s_d.transitions), 3)
        actions = set([a for k, v in s_d.transitions.iteritems() for (a, _, _) in v])
        self.assertEqual(actions, set(['drive_to(e)', 'drive_to(f)', 'drive_to(g)']))
        self.assertEqual(list(planner._get_next_actions()), ['drive_to(b)'])
        self.assertEqual(list(planner.get_best_actions()), ['drive_to(b)'])
        self.assertEqual(planner.get_best_plan(),
                         [['drive_to(b)'], ['drive_to(d)'], ['drive_to(g)'], ['drive_to(h)'], ['drive_to(o)'], ['drive_to(p)']])
        planner0 = planner
        planner = Planner(facts0, domain, min_sample_size=50)

        s_b = State(facts=[
            Fact(o='_', a='curpos', v='b'),
            Fact(o='_', a='curtime', v='5'),
            Fact(o='_', a='goalpos', v='p'),
        ])
        self.assertTrue(s_b in planner0._states_prior)
        self.assertTrue(s_b not in planner._states_prior)

        # Start new planner.
        plan_iter = planner.plan()

        # Plan for a few iterations.
        for _ in range(3):
            plan_iter.next()
            print('eval:', sorted(planner._env.facts))

        # At this point, d and c are pending evaluation.
        planner.update(state=s_b, action='drive_to(b)')

        s_d = State(facts=[
            Fact(o='_', a='curpos', v='d'),
            Fact(o='_', a='curtime', v='15'),
            Fact(o='_', a='goalpos', v='p'),
        ])
        planner.update(state=s_d, action='drive_to(d)')

        # At this point, the pending c evaluation should have been pruned,
        # since we've passed the only branch leading to it.
        self.assertEqual(len(planner._state_heap), 1)
        best_plan = planner.get_best_plan()
        print('best plan:', best_plan)
        self.assertEqual(best_plan, None)

        # Plan for a few more iterations.
        for _ in range(10):
            print(planner._state_count)
            plan_iter.next()
            print('eval:', sorted(planner._env.facts))

        print(sorted(planner._current_facts))
        best_plan = planner.get_best_plan()
        self.assertEqual(planner.hopeful, True)

        # Plan until we run out of states.
        try:
            for _ in range(50):
                print(planner._state_count)
                plan_iter.next()
                print('eval:', sorted(planner._env.facts))
            raise Exception("Iteration did not stop.")
        except StopIteration:
            pass
        best_plan = planner.get_best_plan()
        self.assertEqual(planner.hopeful, False)
        self.assertEqual(planner.pending, False)
        self.assertEqual(best_plan, [['drive_to(g)'], ['drive_to(h)'], ['drive_to(o)'], ['drive_to(p)']])

        # Choose a sub-optimal action not part of the best plan, and confirm
        # that re-planning occurs.
        s_f = State(facts=[
            Fact(o='_', a='curpos', v='f'),
            Fact(o='_', a='curtime', v='20'),
            Fact(o='_', a='goalpos', v='p'),
        ])
        planner.update(state=s_f, action='drive_to(f)')
        print(sorted(planner._current_facts))
        self.assertEqual(planner.pending, False)

        best_plan = planner.get_best_plan()
        self.assertEqual(best_plan,
            [['drive_to(i)'], ['drive_to(j)'], ['drive_to(l)'], ['drive_to(o)'], ['drive_to(p)']])


        import yaml
        domain_yml = yaml.dump(domain, indent=4, width=80)#, default_flow_style=0)
        open('domains/driving/domain.yml', 'w').write(domain_yml)

        #TODO:load from yaml

if __name__ == '__main__':
    unittest.main()
