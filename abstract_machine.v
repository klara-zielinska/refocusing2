Module Type ABSTRACT_MACHINE.

  Parameters term configuration value : Set.
  Parameter c_init  : term -> configuration.
  Parameter c_final : value -> configuration.
  Parameter transition : configuration -> configuration -> Prop.


  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), 
                   transition c0 c1 -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), 
                   transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.

End ABSTRACT_MACHINE.