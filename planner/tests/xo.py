"""
2010.9.1 CKS
A solution for the mind-switching problem exemplified in
http://en.wikipedia.org/wiki/The_Prisoner_of_Benda
http://theinfosphere.org/The_Prisoner_of_Benda

-todo:estimate the total number of remaining swaps, and abort if not enough?
"""
from __future__ import print_function, absolute_import

import unittest
import copy

# sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from ..sexpr import se

from ..planner import Planner, Domain, State, Fact, Fitness, Operator, Labeler

#import driving

class Test(unittest.TestCase):

    def setUp(self):
        # Clear instance caches.
        State.STATES.clear()
        Fact.FACTS.clear()

    def test_domain_create_facts(self):
        import uuid
        facts = Fact.from_sexpr("""
            (?game=uuid status ongoing)
            (?game domain xo)
            (?game board ?board=uuid)

            (?board pos0 ?pos0=uuid)
            (?pos0 index 0)
            (?pos0 color e)

            (?board pos1 ?pos1=uuid)
            (?pos1 index 1)
            (?pos1 color e)
        """, functions={'uuid': lambda: str(uuid.uuid4())})
        facts = list(facts)
        fact_keys = set()
        for fact in facts:
            fact_keys.add(fact.unique_key())
        self.assertEqual(len(facts), 9)
        self.assertEqual(len(fact_keys), 9)

    def test_xo(self):

        domain = Domain(name='xo')
        self.assertTrue(domain.module)

        # Define operator.
        op_allowable_move_x = Operator(
            name='mark_x',
            parameters=['?game', '?index'],
            conditions=se("""(
                (?game status ongoing)
                (?game ?index e)
                (?game turn x)
                (?game moves ?moves)
            )"""),
            effects=se("""(
                (branch)
                (change (?game status check))
                (change (?game ?index x))
                (change (?game turn o))
                (change (?game moves (+ ?moves 1)))
            )""")
            )
        #pprint(str2sexpr(op_allowable_move_x._clips_lhs_cleanppform()), indent=4)
        domain.add_operator(op_allowable_move_x)

        op_allowable_move_o = Operator(
            name='mark_o',
            parameters=['?game', '?index'],
            conditions=se("""(
                (?game status ongoing)
                (?game ?index e)
                (?game turn o)
                (?game moves ?moves)
            )"""),
            effects=se("""(
                (branch)
                (change (?game status check))
                (change (?game ?index o))
                (change (?game turn x))
                (change (?game moves (+ ?moves 1)))
            )""")
            )
        domain.add_operator(op_allowable_move_o)

        op_check_game_over = Operator(
            name='check_game_over',
            parameters=['?game'],
            conditions=se("""(

                (?game status check)

                (?game pos0 ?c0)
                (?game pos1 ?c1)
                (?game pos2 ?c2)
                (?game pos3 ?c3)
                (?game pos4 ?c4)
                (?game pos5 ?c5)
                (?game pos6 ?c6)
                (?game pos7 ?c7)
                (?game pos8 ?c8)

                (test (or
                    (eq ?c0 ?c1 ?c2 x)
                    (eq ?c3 ?c4 ?c5 x)
                    (eq ?c6 ?c7 ?c8 x)
                    (eq ?c0 ?c3 ?c6 x)
                    (eq ?c1 ?c4 ?c7 x)
                    (eq ?c2 ?c5 ?c8 x)
                    (eq ?c0 ?c4 ?c8 x)
                    (eq ?c2 ?c4 ?c6 x)
                    (eq ?c0 ?c1 ?c2 o)
                    (eq ?c3 ?c4 ?c5 o)
                    (eq ?c6 ?c7 ?c8 o)
                    (eq ?c0 ?c3 ?c6 o)
                    (eq ?c1 ?c4 ?c7 o)
                    (eq ?c2 ?c5 ?c8 o)
                    (eq ?c0 ?c4 ?c8 o)
                    (eq ?c2 ?c4 ?c6 o)
                ))

            )"""),
            effects=se("""(
                (branch)
                (change (?game status over))
            )""")
            )
        #pprint(str2sexpr(op_check_game_over._clips_lhs_cleanppform()), indent=4)
        domain.add_operator(op_check_game_over)

        op_check_game_ongoing = Operator(
            name='check_game_ongoing',
            parameters=['?game'],
            conditions=se("""(

                (?game status check)

                (?game pos0 ?c0)
                (?game pos1 ?c1)
                (?game pos2 ?c2)
                (?game pos3 ?c3)
                (?game pos4 ?c4)
                (?game pos5 ?c5)
                (?game pos6 ?c6)
                (?game pos7 ?c7)
                (?game pos8 ?c8)

                (test (not (or
                    (eq ?c0 ?c1 ?c2 x)
                    (eq ?c3 ?c4 ?c5 x)
                    (eq ?c6 ?c7 ?c8 x)
                    (eq ?c0 ?c3 ?c6 x)
                    (eq ?c1 ?c4 ?c7 x)
                    (eq ?c2 ?c5 ?c8 x)
                    (eq ?c0 ?c4 ?c8 x)
                    (eq ?c2 ?c4 ?c6 x)
                    (eq ?c0 ?c1 ?c2 o)
                    (eq ?c3 ?c4 ?c5 o)
                    (eq ?c6 ?c7 ?c8 o)
                    (eq ?c0 ?c3 ?c6 o)
                    (eq ?c1 ?c4 ?c7 o)
                    (eq ?c2 ?c5 ?c8 o)
                    (eq ?c0 ?c4 ?c8 o)
                    (eq ?c2 ?c4 ?c6 o)
                )))

            )"""),
            effects=se("""(
                (branch)
                (change (?game status ongoing))
            )""")
            )
        #pprint(str2sexpr(op_check_game_ongoing._clips_lhs_cleanppform()), indent=4)
        domain.add_operator(op_check_game_ongoing)

        domain.fitness = Fitness(conditions=se("""(
                (?game turn ?turn)
                (?game moves ?moves)
                (?game mycolor ?mycolor)
                (?game pos0 ?c0)
                (?game pos1 ?c1)
                (?game pos2 ?c2)
                (?game pos3 ?c3)
                (?game pos4 ?c4)
                (?game pos5 ?c5)
                (?game pos6 ?c6)
                (?game pos7 ?c7)
                (?game pos8 ?c8)
            )"""),
            expr="fitness(**kwargs)")

        domain.labeler = Labeler(conditions=se("""(
                (?game turn ?turn)
                (?game mycolor ?mycolor)
            )"""),
            labels=[
                'expected_fitness_default',
                'expected_fitness_aggregator',
            ],
            expr="label_state(**kwargs)")

        var_map = {}
        facts = Fact.from_sexpr("""
            (?game=game_uuid status ongoing)

            (?game pos0 e)
            (?game pos1 e)
            (?game pos2 e)
            (?game pos3 e)
            (?game pos4 e)
            (?game pos5 e)
            (?game pos6 e)
            (?game pos7 e)
            (?game pos8 e)

            (?game turn x)
            (?game mycolor x)
            (?game moves 0)
        """, functions=domain.module.__dict__, var_map=var_map)
        facts0 = list(facts)
        fact_keys = set()
        for f in facts0:
            fact_keys.add(f.unique_key())
        self.assertEqual(len(facts0), 13)
        self.assertEqual(len(fact_keys), 13)
        planner = Planner(facts0, domain, min_sample_size=1000000, debug=1)
        #env = Environment(facts0, domain=domain)
        env = planner._env
        s0 = env.state
        self.assertEqual(env.fitness(), 0.1)

        # Only the w
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(env._match_sets_clean, True)
        match_sets = copy.deepcopy(env.match_sets)
        self.assertEqual(env._match_sets_clean, True)
        op0_matchsets = match_sets[ops[0].name]

        game_id = var_map['game']

        # Make first move.
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'mark_x')
        s1 = env.update(
            action='mark_x(%s,%s)' % (game_id, 'pos4'),
            changelist=[
                Fact(o=game_id, a='turn', v='o'),
                Fact(o=game_id, a='moves', v=1),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos4', v='x'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)
        self.assertAlmostEqual(env.fitness(), 0.09, 2)

        labels = planner._env.labels()
        self.assertEqual(labels,
            {'expected_fitness_aggregator': min,
             'expected_fitness_default': 1e999999})

        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_ongoing')
        s1b = env.update(
            action='check_game_ongoing(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='ongoing'),
            ])
        planner._push_state()

        # Make 2nd move.
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'mark_o')
        s2 = env.update(
            action='mark_o(%s,%s)' % (game_id, 'pos0'),
            changelist=[
                Fact(o=game_id, a='turn', v='x'),
                Fact(o=game_id, a='moves', v=2),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos0', v='o'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)

        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_ongoing')
        s2b = env.update(
            action='check_game_ongoing(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='ongoing'),
            ])
        planner._push_state()

        # Make 3rd move.
        s3 = env.update(
            action='mark_x(%s,%s)' % (game_id, 'pos2'),
            changelist=[
                Fact(o=game_id, a='turn', v='o'),
                Fact(o=game_id, a='moves', v=3),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos2', v='x'),
            ])
        planner._push_state()

        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_ongoing')
        s3b = env.update(
            action='check_game_ongoing(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='ongoing'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)

        # Make 4th move.
        s4 = env.update(
            action='mark_o(%s,%s)' % (game_id, 'pos3'),
            changelist=[
                Fact(o=game_id, a='turn', v='x'),
                Fact(o=game_id, a='moves', v=4),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos3', v='o'),
            ])
        planner._push_state()

        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_ongoing')
        s4b = env.update(
            action='check_game_ongoing(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='ongoing'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)

        # Make 5th move.
        s5 = env.update(
            action='mark_x(%s,%s)' % (game_id, 'pos6'),
            changelist=[
                Fact(o=game_id, a='turn', v='o'),
                Fact(o=game_id, a='moves', v=5),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos6', v='x'),
            ])
        planner._push_state()

        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_over')
        s5b = env.update(
            action='check_game_over(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='over'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)
        self.assertAlmostEqual(env.fitness(), 0.94, 2)

        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 0)

        # Backup to state 4.
        planner._env.switch(s4)
#        domain.module.print_board(env.state)

        # Make 5.2th move.
        s52 = env.update(
            action='mark_x(%s,%s)' % (game_id, 'pos8'),
            changelist=[
                Fact(o=game_id, a='turn', v='o'),
                Fact(o=game_id, a='moves', v=5),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos8', v='x'),
            ])
        planner._push_state()
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_ongoing')
        s52b = env.update(
            action='check_game_ongoing(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='ongoing'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)

        # Make 5.2.1th move.
        s521 = env.update(
            action='mark_o(%s,%s)' % (game_id, 'pos6'),
            changelist=[
                Fact(o=game_id, a='turn', v='x'),
                Fact(o=game_id, a='moves', v=6),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos6', v='o'),
            ])
        planner._push_state()
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_over')
        s521b = env.update(
            action='check_game_over(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='over'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)

        # Backup to state 5.2.
        planner._env.switch(s52)
#        domain.module.print_board(env.state)

        # Make 5.2.1th move.
        s521 = env.update(
            action='mark_o(%s,%s)' % (game_id, 'pos1'),
            changelist=[
                Fact(o=game_id, a='turn', v='x'),
                Fact(o=game_id, a='moves', v=6),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos1', v='o'),
            ])
        planner._push_state()
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_ongoing')
        s521b = env.update(
            action='check_game_ongoing(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='ongoing'),
            ])
        planner._push_state()
#        domain.module.print_board(env.state)

        s522 = env.update(
            action='mark_x(%s,%s)' % (game_id, 'pos5'),
            changelist=[
                Fact(o=game_id, a='turn', v='o'),
                Fact(o=game_id, a='moves', v=7),
                Fact(o=game_id, a='status', v='check'),
                Fact(o=game_id, a='pos5', v='x'),
            ])
        planner._push_state()
        ops = list(env.activated_operators)
        self.assertEqual(len(ops), 1)
        self.assertEqual(ops[0].name, 'check_game_over')
        s52b = env.update(
            action='check_game_over(%s)' % (game_id,),
            changelist=[
                Fact(o=game_id, a='status', v='over'),
            ])
        planner._push_state()

        #domain.module.print_board(s52)
        # The currently explored actions after state s52 are
        # the enemy winning (fitness=0.03) and the enemy making a mistake
        # leading to our eventual victory (fitness=0.92).
        # Since this is the enemy's turn, and it's trying to minimize our
        # eventual score, the expected fitness at this state should be
        # min(0.03,0.92) == 0.03.
        print(planner._state_expected_fitness[s52])
        self.assertAlmostEqual(planner._state_expected_fitness[s3], 0.94, 2)
        self.assertAlmostEqual(planner._state_expected_fitness[s52], 0.03, 2)

        print('expected fitness:')
        for state, fitness in planner._state_expected_fitness.iteritems():
            domain.module.print_board(state)
            print('%.2f' % fitness)

        # Auto-plan best move.
        print('='*80)
        planner = Planner(facts0, domain, min_sample_size=1000000, debug=1)
        plan_iter = planner.plan()
        self.assertEqual(planner.pending, True)
        try:
            for _ in xrange(9*50):
                plan_iter.next()
                if not _ % 10:
                    print(planner._state_count)
        except StopIteration:
            print('stopped planning')
        self.assertEqual(planner.hopeful, True)
        self.assertEqual(planner.pending, True)
        best_plan = planner.get_best_plan()
        print('best plan:', best_plan)

        import yaml
        domain_yml = yaml.dump(domain, indent=4, width=80)#, default_flow_style=0)
        open('domains/xo/domain.yml', 'w').write(domain_yml)

if __name__ == '__main__':
    unittest.main()
