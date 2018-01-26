import uuid as _uuid

uuid = lambda: str(_uuid.uuid4()).replace('-', '').strip()

def fitness(env, problem_id, actioncount):
    """
    Value goes to 0.0 the more all minds and bodies match.
    Otherwise, goes to 1.0.
    Preference is given to a solution involving fewer swap actions.
    """
    actioncount = int(actioncount)
    #print 'actioncount:',actioncount

    all_goals = env.match_sets.get(env.domain.fitness.get_collector('all-goals').rule_id, [])
    #print 'all_goals:',all_goals
    all_goals_met = env.match_sets.get(env.domain.fitness.get_collector('all-goals-met').rule_id, [])
    #print 'all_goals_met:',all_goals_met

    corrected_ratio = len(all_goals_met)/float(len(all_goals))
    parts = [0.9*corrected_ratio, 0.1*(1/(actioncount+1.0))]
    #print 'score parts:',parts
    score = 1 - sum(parts)
    #print 'score:',score
    return score
