import uuid as _uuid

uuid = lambda: str(_uuid.uuid4())

def fitness(state, swapcount):
    """
    """
#    (* 0.9
#        ; Calculate ratio of entities with a correct mindbody correlation.
#        ; i.e. count(entities with a matching mindbody fact)/count(all entities)
#        (/
#            (/ (length (find-all-facts ((?e entity)(?m mindbody)) (and (eq ?e:mind ?m:mind) (eq ?e:body ?m:body)))) 2)
#            (length (find-all-facts ((?e entity)) TRUE))
#        )
#    )
    entity_count = state.get_entities #TODO
    correct_entity_count = state.get_correct_entities #TODO
    corrected_ratio = entity_count/float(correct_entity_count)
    return 0.9*corrected_ratio + 0.1*(1/(swapcount+1))