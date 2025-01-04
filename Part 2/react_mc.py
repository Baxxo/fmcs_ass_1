import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque

from pynusmv.dd import BDD, State
from pynusmv.fsm import BddFsm
from pynusmv.prop import Spec

from typing import List, Tuple, Optional

specTypes = {
    'LTLSPEC': parser.TOK_LTLSPEC,
    'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES,
    'IFF': parser.IFF,
    'OR': parser.OR,
    'XOR': parser.XOR,
    'XNOR': parser.XNOR,
    'AND': parser.AND,
    'NOT': parser.NOT,
    'ATOM': parser.ATOM,
    'NUMBER': parser.NUMBER,
    'DOT': parser.DOT,
    'NEXT': parser.OP_NEXT,
    'OP_GLOBAL': parser.OP_GLOBAL,
    'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL,
    'NOTEQUAL': parser.NOTEQUAL,
    'LT': parser.LT,
    'GT': parser.GT,
    'LE': parser.LE,
    'GE': parser.GE,
    'TRUE': parser.TRUEEXP,
    'FALSE': parser.FALSEEXP
}

basicTypes = {
    parser.ATOM,
    parser.NUMBER,
    parser.TRUEEXP,
    parser.FALSEEXP,
    parser.DOT,
    parser.EQUAL,
    parser.NOTEQUAL,
    parser.LT,
    parser.GT,
    parser.LE,
    parser.GE
}

booleanOp = {
    parser.AND,
    parser.OR,
    parser.XOR,
    parser.XNOR,
    parser.IMPLIES,
    parser.IFF
}

def spec_to_bdd(model : BddFsm, spec : Spec) -> BDD:
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`.
    The `model` is a symbolic representation of the loaded smv program that can be
    obtained with `pynusmv.glob.prop_database().master.bddFsm`.
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec
    
def is_boolean_formula(spec : Spec) -> bool :
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False
    
def is_GF_formula(spec : Spec) -> bool:
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a 
    boolean combination of base formulas with no temporal operators.
    Returns True if `spec` is in the correct form, False otherwise 
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return False
    return is_boolean_formula(spec.car)

def parse_implication(spec : Spec) -> bool:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a simple 
    reactivity formula, that is wether the formula is of the form
    
                    GF f -> GF g
    
    where f and g are boolean combination of basic formulas.
    """
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return False
    # Check if lhs and rhs of the implication are GF formulas
    return is_GF_formula(spec.car) and is_GF_formula(spec.cdr)
    
def parse_react(spec : Spec) -> bool:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a Reactivity 
    formula, that is wether the formula is of the form
    
        (GF f_1 -> GF g_1) & ... & (GF f_n -> GF g_n)
    
    where f_1, ..., f_n, g_1, ..., g_n are boolean combination of basic formulas.
    
    Returns True if `spec` is a Reactivity formula, False otherwise.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # check all conjuncts of the main formula
    working = deque()
    working.append(spec)
    while working:
        # next formula to analyse
        head = working.pop()
        if head.type == specTypes['AND']:
            # push conjuncts into the queue
            working.append(head.car)
            working.append(head.cdr)
        else:
            # check if it is a GF f -> GF g formula
            if not parse_implication(head):
                return False
    # if we are here, all conjuncts are of the correct form
    return True

def check_explain_react_spec(spec : Spec):
    if not parse_react(spec):
        return None
    return pynusmv.mc.check_explain_ltl_spec(spec)

def build_implies_formula_list(spec : Spec) -> List[Spec]:
    if not parse_react(spec):
        return []
    
    ret : List[Spec] = []

    spec = spec.cdr
    # check all conjuncts of the main formula
    working = deque()
    working.append(spec)
    while working:
        # next formula to analyse
        head = working.pop()
        #print("head: ", head)

        if head.type == specTypes['AND']:
            # push conjuncts into the queue
            working.append(head.car)
            working.append(head.cdr)

        if head.type == specTypes['IMPLIES']:
            ret.insert(0, head)
    return ret

def get_components_of_implies_spec(spec : Spec) -> Optional[Tuple[Spec, Spec]]:
    """
    If the given specification `spec` is a formula on the form

                    GF f -> GF g

    where f and g are boolean combination of basic formulas this function returns the
    tuple (f, g).

    If the specification is not in that form then the function returns None
    """
    if not parse_implication(spec):
        return None
    
    f : Spec = spec.car.car.car
    g : Spec = spec.cdr.car.car

    return (f, g)

def get_reachable_states(model : BddFsm) -> BDD:
    """
    Given a `BddFsm` this function returns a `BDD` of all the reachable states of the `BddFsm`
    """
    reach : BDD = model.init
    new : BDD = model.init
    while model.count_states(new) > 0:
        new = model.post(new) - reach
        reach = reach | new
    return reach

def get_cycle(model : BddFsm, recur : BDD, pre_reach : BDD) -> Tuple[State, List[State]]:
    """
    Given a `BddFsm` and two `BDD`'s in which there is an infinite path, this functon returns
    a tuple where the first element is the state where the cycle starts and a list of all
    the states that compose the cycle.
    """

    s : State = model.pick_one_state_random(recur)

    exit : bool = False

    while not exit:
        r : BDD = BDD.false(model)
        new : BDD = model.post(s) & pre_reach
        new_list : List[BDD] = [new]

        while model.count_states(new) > 0:
            r = r | new
            new = model.post(new) & pre_reach
            new = new - r
            new_list.append(new)
        
        r = r & recur

        if s.entailed(r):
            exit = True
            break
        else:
            s = model.pick_one_state_random(r)
    
    k = -1
    for i in range(0, len(new_list)):
        if s.entailed(new_list[i]):
            k = i
            break
    
    path : List[State] = [s]
    curr : State = s

    for i in range(k - 1, -1, -1):
        Pred = model.pre(curr) & new_list[i]
        curr = model.pick_one_state_random(Pred)
        path.insert(0, curr)
    
    path.insert(0, s)

    return s, path

def get_prefix (model : BddFsm, s : State) -> List[State]:
    """
    Given a `BddFsm` and a `State` reachable from the `BddFsm` this function returns a
    path from an initial state to the given `State`
    """
    new : BDD = model.init
    reach : BDD = model.init
    trace : List[BDD] = [new]

    while not s.entailed(new):
        new = model.post(new) - reach
        reach = reach | new
        trace.append(new)

    if len(trace) < 1:
        return []

    prefix : List[State] = []
    current_state = s

    for i in range(len(trace) - 2, -1, -1):
        current_state = model.pick_one_state_random(
            model.pre(current_state) & trace[i]
        )

        prefix.insert(0, current_state)

    return prefix

def reactiveness_symbolic_repeatability(model : BddFsm, f : BDD, g : BDD) -> Tuple[bool, Optional[List[State]], Optional[int]]:
    """
    Given a `BddFsm` and two `BDD`'s representing the two components of a reactive formula

                    GF f -> GF g
    
    this function returns a tuple in this form:
        - The first element indicates whether the formula holds
        - The second element, if the first is `True`, is a list of states that compose the
          counterexample in a lasso-shaped form: a prefix and a cycle.
          If the first element is `False` then this element is `None`.
        - The third element is the length of the prefix of the counterexample.
          If the first element is `False` then this element is `None`
    """
    reach : BDD = get_reachable_states(model)

    recur : BDD = reach & f & ~g

    while model.count_states(recur) > 0:
        new = model.pre(recur) & ~g
        pre_reach : BDD = BDD.false(model)

        while model.count_states(new) > 0:
            pre_reach = pre_reach | new
            
            if recur.entailed(pre_reach):
                s, cycle = get_cycle(model, recur, pre_reach)
                prefix = get_prefix(model, s)

                #print("Lenght of the prefix: ", len(prefix))
                #print("Lenght of the cycle: ", len(cycle))

                return True, (prefix + cycle), len(prefix)
            
            new = (model.pre(new) & ~g) - pre_reach
        
        recur = recur & pre_reach

    return False, None, None

def my_check_explain_react_spec(model : BddFsm, spec : Spec) -> Optional[Tuple[bool, Optional[List[dict]]]]:
    """
    Returns whether the loaded SMV model satisfies or not the reactivity formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. Returns also an explanation for why the model does not satisfy
    `spec`, if it is the case.

    The result is `None` if `spec` is not a reactivity formula, otherwise it is a 
    tuple where the first element is a boolean telling whether `spec` is satisfied,
    the second element is either `None` if the first element is `True`, or an execution
    of the SMV model violating `spec` otherwise and the third element is the length of
    the prefix of the counterexample if the first element is `True`, `None` otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. The execution is looping: the last state should be 
    somewhere else in the sequence. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    if not parse_react(spec):
        return None
    
    reactivity_formulas = build_implies_formula_list(spec)

    for f in reactivity_formulas:
        #print("Formula: ", f)

        f_spec, g_spec = get_components_of_implies_spec(f)

        f_bdd = spec_to_bdd(model, f_spec)
        g_bdd = spec_to_bdd(model, g_spec)

        result, states_list, prefix_length = reactiveness_symbolic_repeatability(model, f_bdd, g_bdd)

        if result:
            counterexample : List[dict] = [states_list[0].get_str_values()]

            #print("Lenght of states_list: ", len(states_list))
            
            for i in range(0, len(states_list) - 1):
                curr = states_list[i]
                next = states_list[i+1]
                input = model.pick_one_inputs_random(
                    model.get_inputs_between_states(curr, next)
                )
                counterexample.append(input.get_str_values())
                counterexample.append(next.get_str_values())

            return False, counterexample, (prefix_length * 2)
        
    return True, None

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        #print("\n")
        print("spec: ", spec)

        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        
        """
        res = check_explain_react_spec(spec)
        if res == None:
            print('Property is not a Reactivity formula, skipping')
        elif res[0] == True:
            print("Library result: ", "Property is respected")
        elif res[0] == False:
            print("Library result: ", "Property is not respected")
            print("Counterexample:", res[1])
        """

        model = pynusmv.glob.prop_database().master.bddFsm
        my_res = my_check_explain_react_spec(model, spec)
        if my_res == None:
            print('Property is not a Reactivity formula, skipping')
        elif my_res[0] == True:
            print("Result: ", "Property is respected")
        elif my_res[0] == False:
            print("Result: ", "Property is not respected")
            print("Counterexample:")

            for i in range(0, len(my_res[1])):
                if i == my_res[2]:
                    print("*-*-*-*-*-* LOOP STARTS HERE *-*-*-*-*-*")
                print(" ", my_res[1][i])
        print("\n")
        
    pynusmv.init.deinit_nusmv()
