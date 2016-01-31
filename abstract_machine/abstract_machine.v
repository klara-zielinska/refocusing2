Require Import Util
               Entropy.
Require Export rewriting_system.




Module Type ABSTRACT_MACHINE.

  Parameters 
  (term          : Set)
  (configuration : Set)
  (value         : Set)

  (load          : term -> configuration)
  (value_to_conf : value -> configuration)
  (final         : configuration -> option value)
  (transition    : configuration -> configuration -> Prop)
  (next_conf     : entropy -> configuration -> option configuration).

  Coercion value_to_conf : value >-> configuration.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Axioms
  (final_correct :                                                              forall c,
       final c <> None -> ~exists c', c → c')
  (trans_computable :                                                       forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2)
  (finals_are_vals :                                                          forall c v,
       final c = Some v <-> c = v).



  Class SafeRegion (P : configuration -> Prop) :=
  { 
      preservation :                                                        forall c1 c2,
          P c1  ->  c1 → c2  ->  P c2;
      progress :                                                               forall c1,
          P c1  ->  (exists (v : value), c1 = v) \/ (exists c2, c1 → c2)
  }.

End ABSTRACT_MACHINE.




Module Type ABSTRACT_MACHINE_DET (AM : ABSTRACT_MACHINE).

  Include AM.

  Axiom trans_det :                                                      forall c1 c2 c3,
      c1 → c2  ->  c1 → c3  ->  c2 = c3.

End ABSTRACT_MACHINE_DET.
