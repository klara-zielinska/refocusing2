Require Import Util.
Require Import rewriting_system.
Require Import Entropy.





Module Type ABSTRACT_MACHINE <: REWRITING_SYSTEM.

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

  Notation "c1 → c2"  := (transition c1 c2)              (no associativity, at level 70).
  Notation "t1 →+ t2" := (clos_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).
  Notation "t1 →* t2" := (clos_refl_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).

  Axioms
  (final_correct :                                                              forall c,
       final c <> None -> ~exists c', c → c')
  (trans_computable :                                                       forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2)
  (finals_are_vals :                                                          forall c v,
       final c = Some v <-> c = v).

End ABSTRACT_MACHINE.




Module Type ABSTRACT_MACHINE_DET (AM : ABSTRACT_MACHINE).

  Include AM.

  Axiom trans_det : forall c1 c2 c3, c1 → c2 -> c1 → c3 -> c2 = c3.

End ABSTRACT_MACHINE_DET.




Module Type AM_SAFE_REGION (AM : ABSTRACT_MACHINE).

  Import AM.

  Parameter safe : configuration -> Prop.

  Axioms
  (preservation :                                                           forall c1 c2,
       safe c1 -> c1 → c2 -> safe c2)
  (progress :                                                                   forall c,
       safe c -> (exists v, c = v) \/ (exists c', c → c')).

End AM_SAFE_REGION.




Module Type AM_PROGRESS (AM : ABSTRACT_MACHINE).

  Import AM.

  Axiom progress :                                                            forall t c,
      (load t →* c) -> (exists v, c = v) \/ (exists c', c → c').

End AM_PROGRESS.
