import uuid as _uuid

uuid = lambda: str(_uuid.uuid4())

def fitness(env, problem_id, swapcount):
    """
    Value goes to 1.0 the more all minds and bodies match.
    Otherwise, goes to 0.0.
    Preference is given to a solution involving fewer swap actions.
    """
    swapcount = int(swapcount)
#    (* 0.9
#        ; Calculate ratio of entities with a correct mindbody correlation.
#        ; i.e. count(entities with a matching mindbody fact)/count(all entities)
#        (/
#            (/ (length
#                (find-all-facts ((?e entity)(?m mindbody)) (and (eq ?e:mind ?m:mind) (eq ?e:body ?m:body)))
#            ) 2)
#            (length (find-all-facts ((?e entity)) TRUE))
#        )
#    )
    state = env.state
    entity_count = len(state.find_facts(o=problem_id, a='entity'))
    correct_entity_count = len(env.match_sets.get(env.domain.fitness.get_collector('mind-body-matches').rule_id))
    corrected_ratio = entity_count/float(correct_entity_count)
    return 0.9*corrected_ratio + 0.1*(1/(swapcount+1.0))