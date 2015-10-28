Module Type ABSTRACT_MACHINE.

  Parameters term configuration value : Set.

  Parameter c_init  : term -> configuration.
  Parameter c_final : value -> configuration.

  Parameter transition : configuration -> configuration -> Prop.
  Notation "c1 → c2" := (transition c1 c2) (at level 40, no associativity).

  Axiom final_correct : forall v c, ~ c_final v → c.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).


  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.

End ABSTRACT_MACHINE.




Module Type DET_ABSTRACT_MACHINE <: ABSTRACT_MACHINE.

  Include ABSTRACT_MACHINE.

  Parameter next_conf : configuration -> option configuration.
  Axiom next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

End DET_ABSTRACT_MACHINE.




Module Type AM_SAFETY (AM : ABSTRACT_MACHINE).

  Import AM.

  Parameter good_conf : configuration -> Prop.

  Axiom preservation : forall c1 c2, good_conf c1 -> c1 → c2 -> good_conf c2.
  Axiom progress     : forall c, good_conf c -> 
                           (exists v, c = c_final v) \/ (exists c', c → c').

End AM_SAFETY.
