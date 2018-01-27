import uuid as _uuid

uuid = lambda: str(_uuid.uuid4()).replace('-', '').strip()

def fitness(env, problem_id, actioncount, all_goals=None, all_goals_met=None):
    """
    Value goes to 0.0 the more all block positions are reached..
    Otherwise, goes to 1.0.
    Preference is given to a solution involving fewer block actions.
    """
    actioncount = int(actioncount)
    #print 'actioncount:',actioncount

    if all_goals is None:
        all_goals = env.match_sets.get(env.domain.fitness.get_collector('all-goals').rule_id, [])
    #print 'all_goals:',all_goals

    if all_goals_met is None:
        all_goals_met = env.match_sets.get(env.domain.fitness.get_collector('all-goals-met').rule_id, [])
    #print 'all_goals_met:',all_goals_met

    # For three blocks, a perfect score would be 3 positions in 3 moves.
    corrected_ratio = len(all_goals_met)/float(len(all_goals)) # ideal of 1.0
    parts = [0.9*corrected_ratio, 0.1*((len(all_goals)+1)/(actioncount+1.0))]
    #print 'score parts:',parts
    score = 1 - min(sum(parts), 1.0)
    #print 'score:',score
    return score
