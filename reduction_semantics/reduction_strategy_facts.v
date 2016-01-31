Require Import reduction_strategy.



Module RED_STRATEGY_STEP_Facts (R : RED_STRATEGY_LANG) (ST : RED_STRATEGY_STEP R).

  Import R ST.


  Lemma dec_term_val_alive :                                                forall t k v,
      dec_term t k = in_val v -> ~dead_ckind k.

  Proof.
    intros t k v H H0.
    assert (dec_term t k = in_dead) by auto using dec_term_from_dead.
    congruence.
  Qed.


  Lemma dec_context_val_alive :                                        forall ec k v0 v1,
      dec_context ec k v0 = in_val v1 -> ~dead_ckind k.

  Proof.
    intros ec k v0 v1 H H0.
    assert (dead_ckind (k+>ec))            by auto using death_propagation.
    assert (dec_context ec k v0 = in_dead) by auto using dec_context_from_dead.
    congruence.
  Qed.


End RED_STRATEGY_STEP_Facts.

  

