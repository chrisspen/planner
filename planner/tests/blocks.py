from __future__ import print_function, absolute_import

import unittest
from pprint import pprint

# sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

from sexpr import se

from .. import planner as p

class Test(unittest.TestCase):

    def setUp(self):
        # Clear instance caches.
        p.State.STATES.clear()
        p.Fact.FACTS.clear()
        p.Domain.DOMAINS.clear()

    def test_domain(self):

        domain = p.Domain(name='blocks')
        self.assertTrue(domain.module)

        # Define operator.
        op_unstack = p.Operator(
            name='unstack',
            parameters=['?block1'],
            conditions=[
                ['?problem', 'actioncount', '?count'],
                ['?problem', 'block', '?block1'],

                # To unstack block1, it must be ontop of something other than the table.
                ['?problem', 'current', '?placement1'],
                ['?placement1', 'top', '?block1'],
                ['?placement1', 'bot', '?block2'],

                #['?problem', 'current', '?placement2'],
                ['test', ['neq', '?block2', 'TABLE']],

                # To unstack block1, there must not be anything on top of block1.
                se("""(not (and
                    (?problem current ?placement2)
                    (?placement2 top ?othertop)
                    (?placement2 bot ?block1)
                ))"""),
            ],
            effects=[
                ['branch'],
                se("(del (?problem actioncount ?count))"),
                se("(add (?problem actioncount (+ ?count 1)))"),

                # block1 goes ontop of table.
                se("(del (?placement1 bot ?block2))"),
                se("(add (?placement1 bot TABLE))"),
            ])
        domain.add_operator(op_unstack)

        op_stack = p.Operator(
            name='stack',
            parameters=['?block1', '?block2'],
            conditions=[
                ['?problem', 'actioncount', '?count'],
                ['?problem', 'block', '?block1'],
                ['?problem', 'block', '?block2'],

                # Block1 is ontop of something
                ['?problem', 'current', '?placement1'],
                ['?placement1', 'top', '?block1'],
                ['?placement1', 'bot', '?bottom1'],

                # Block2 is ontop of something
                ['?problem', 'current', '?placement2'],
                ['?placement2', 'top', '?block2'],
                ['?placement2', 'bot', '?bottom2'],

                ['test', ['neq', '?block1', '?block2']],

                # To stack block1 onto block2, there must be nothing ontop of block1.
                #['?problem', 'current', '?placement1'],
                se("""(not (and
                    (?problem current ?placement3)
                    (?placement3 top ?top1)
                    (?placement3 bot ?block1)
                ))"""),

                # To stack block1 onto block2, there must be nothing ontop of block2.
                #['?problem', 'current', '?placement2'],
                se("""(not (and
                    (?problem current ?placement4)
                    (?placement4 top ?top2)
                    (?placement4 bot ?block2)
                ))"""),
            ],
            effects=[
                ['branch'],
                se("(del (?problem actioncount ?count))"),
                se("(add (?problem actioncount (+ ?count 1)))"),

                # block1 is no longer ontop of the old thing.
                se("(del (?placement1 bot ?bottom1))"),

                # block1 goes ontop of block2.
                se("(add (?placement1 bot ?block2))"),
            ])
        domain.add_operator(op_stack)

        domain.fitness = p.Fitness(conditions=[
                ['?problem', 'actioncount', '?count'],
            ],
            collectors=[
                p.Collector(
                    'all-goals',
                    [
                        se("(?problem goal ?gp1)"),
                        se("(?gp1 top ?topblock)"),
                        se("(?gp1 bot ?bottomblock)"),
                    ]
                ),
                p.Collector(
                    'all-goals-met',
                    [
                        se("(?problem current ?p1)"),
                        se("(?p1 top ?topblock)"),
                        se("(?p1 bot ?bottomblock)"),
                        se("(?problem goal ?gp1)"),
                        se("(?gp1 top ?topblock)"),
                        se("(?gp1 bot ?bottomblock)"),
                    ]
                )
            ],
            expression="fitness(?env, ?problem, ?count)")

        domain.save('domains/blocks/domain.yml')

    def test_plan(self):

        def show_step():
            print('actions:', cursor.actions)
            print('new states:')
            for state in cursor.new_states:
                print(state)
            pprint(state.get_fact_tree('blocks1'), indent=4)

        def on_new_state(env):
            state = env.state
            print('-'*80)
            print('on_new_state():')
            print('\t\tstate:', state)
            print('\t\tcurrent:')
            show_table(state.get_fact_tree('blocks1'), 'current', prefix='\t\t\t')
            print('\t\tgoal:')
            show_table(state.get_fact_tree('blocks1'), 'goal', prefix='\t\t\t')

        def show_heap():
            print('heap:')
            for fitness, state in planner.iter_heap():
                print('\tfitness:', fitness)
                print('\t\tstate:', state)
                print('\t\tcurrent:')
                show_table(state.get_fact_tree('blocks1'), 'current', prefix='\t\t\t')
                print('\t\tgoal:')
                show_table(state.get_fact_tree('blocks1'), 'goal', prefix='\t\t\t')

        def show_table(tree, type, prefix=''): # pylint: disable=redefined-builtin
            assert type in ('current', 'goal')
            bot_to_top = {} # {thing:thing-on-top}
            top_to_bot = {}
            on_table = []
            for p in tree['blocks1'][type]:
                data = p[p.keys()[0]]
                bot = data['bot']
                top = data['top']
                if bot == 'TABLE':
                    on_table.append(top)
                else:
                    #assert bot not in placements
                    bot_to_top[bot] = top
                    top_to_bot[top] = bot
            pending = list(on_table)
            processed = set()
            rows = []
            thing_to_col = {}
            thing_to_row = {}
            thing_to_coord = {}
            coords = set()
            while pending:
                thing = pending.pop(0)
                if thing in processed:
                    continue
                processed.add(thing)

                bot = top_to_bot.get(thing, 'TABLE')
                bot_coord = thing_to_coord.get(bot, (0, -1))

                # Lookup coordinate.
                coord = (bot_coord[0], bot_coord[1]+1)
                while coord in coords:
                    coord = (coord[0]+1, coord[1])
                coords.add(coord)
                thing_to_coord[thing] = coord

                # Mark thing at coordinate in display.
                x, y = coord
                while len(rows) <= y:
                    rows.append([])
                while len(rows[y]) <= x:
                    rows[y].append(' ')
                rows[y][x] = thing[-1]

                # Queue top thing for display.
                top = bot_to_top.get(thing, None)
                if top:
                    pending.append(top)

            print('\n'.join(reversed([prefix + (''.join(row)) for row in rows])))
            print(prefix + ('-'*len(processed)))

        fn1 = 'domains/blocks/domain.yml'
        domain = p.Domain.load(fn1)

        facts0 = list(p.Fact.from_sexpr_file('domains/blocks/problem1.txt'))

        planner = p.Planner(
            facts=facts0,
            domain=domain,
            estimator=p.AlwaysHopeful(),
            min_sample_size=10,
            debug=1)

        # Pause iteration after each simulated action.
        # This is the smallest possible level of iteration.
        #planner.iter_type = p.ITER_PER_ACTION

        # Pause iteration after each state is fully evaluated.
        planner.iter_type = p.ITER_PER_STATE

        self.assertEqual(len(planner.env.facts), len(facts0))
        self.assertEqual(len(planner.env.state.facts), len(facts0))
        self.assertEqual(planner.debug, True)
        self.assertEqual(planner.pending, True)
        self.assertEqual(len(planner._state_heap), 1)
        self.assertEqual(len(planner._states), 1)

        plan_iter = planner.plan(on_new_state=on_new_state)

        cursor = plan_iter.next()
        # The first state is three blocks stacked ontop of each other,
        # and so should only have a single possible action, to unstack
        # the top block.
#        show_step()
        #self.assertEqual(planner.size, 1)
        self.assertEqual(cursor.actions, ['unstack(blockA)'])

        cursor = plan_iter.next()
        # The second state should have three actions.
#        show_step()
#        show_heap()
        self.assertEqual(planner.size, 3)
        self.assertEqual(
            set(cursor.actions),
            set(['unstack(blockB)', 'stack(blockA,blockB)', 'stack(blockB,blockA)']))

#        try:
#            plan_iter.next()
#            self.assertTrue(0, 'Planner did not stop planning as expected.')
#        except StopIteration:
#            pass

        try:
            for _ in xrange(4):
                print('i:', _)
                #show_heap()
                print('planner.size:', planner.size)
                plan_iter.next()
        except StopIteration:
            pass

        print('best fitness:', planner.best_fitness)
        best_plan = planner.get_best_plan()
        print('best plan:', best_plan)
        self.assertEqual(
            best_plan,
            [['unstack(blockA)'], ['stack(blockB,blockA)'], ['stack(blockC,blockA)']]
        )

if __name__ == '__main__':
    unittest.main()
