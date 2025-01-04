import pynusmv
from pynusmv.fsm import BddFsm
from pynusmv.dd import BDD
from pynusmv.prop import Spec

from typing import Optional, Tuple, List
import sys

def spec_to_bdd(model: BddFsm, spec: Spec) -> BDD:
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec
    
def SymbolicReachable(model : BddFsm, Phi : BDD) -> bool:
    """
    Given a `BddFsm` representing the actual model and a `BDD` representing
    a boolean formula, this function returns whether the formula is
    reachable or not.
    """
    Reach = model.init
    New = model.init
    while model.count_states(New):
        if New.intersected(Phi):
            return True
        New = model.post(New).diff(Reach)
        Reach = Reach | New
    return False

def WitnessReachable (model : BddFsm, Phi: BDD) -> Tuple[bool, Optional[List[dict]]]:
    """
    Given a `BddFsm` representing the actual model and a `BDD` representing
    a boolean formula, this function returns whether the formula is
    reachable or not.
    If the formula is reachable then the function provides also an execution as
    proof of the reachability of the formula.
    """
    Reach = model.init
    New : list[BDD] = [model.init]
    k = 0

    while model.count_states(New[k]):
        if New[k].intersected(Phi):
            s = model.pick_one_state_random(New[k] & Phi)
            path = [s.get_str_values()]
            for i in range(k-1, -1, -1):
                Pred = (model.pre(s)) & New[i]
                pre_s = model.pick_one_state_random(Pred)

                input = model.get_inputs_between_states(pre_s, s)

                path.insert(0, model.pick_one_inputs(input).get_str_values())
                path.insert(0, pre_s.get_str_values())

                s = pre_s
            return (True, path)
        
        New.append((model.post(New[k])).diff(Reach))
        k = k+1
        Reach = New[k] + Reach
        
    return (False, None)


def my_check_explain_inv_spec(model : BddFsm, spec : Spec) -> Tuple[bool, Optional[List[dict]]]:
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The execution is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """

    bdd_spec = spec_to_bdd(model, spec)
    bdd_notspec = bdd_spec.not_()

    # return not SymbolicReachable(model, bdd_notspec)
    res, trace = WitnessReachable(model, bdd_notspec)
    return (not res, trace)

def check_explain_inv_spec(spec):
    ltlspec = pynusmv.prop.g(spec)
    res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)
    return res, trace

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    invtype = pynusmv.prop.propTypes['Invariant']

    model = pynusmv.glob.prop_database().master.bddFsm

    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            
            print("Property", spec, "is an INVARSPEC.")

            """
            print("LIBRARY SOLUTION:")
            res, trace = check_explain_inv_spec(spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(trace)
            print("\n")
            """
            
            #print("SOLUTION:")
            res, trace = my_check_explain_inv_spec(model, spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print("Counterexample: ")
                print("  ", trace)
            print("\n")
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")
            print("\n")

    pynusmv.init.deinit_nusmv()
