Require Import Util.
Require Import reduction_languages_facts.




Module Type DET_RED_MINI_SEM.

  Include RED_MINI_LANG.


  Parameter contract : forall {k}, redex k -> option term.


  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red _ r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.

  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.

  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].

  Notation "k |~ t1 → t2"  := (reduce k t1 t2)   (no associativity, at level 70).
  Notation "k |~ t1 →+ t2" := (clos_trans_1n _ (reduce k) t1 t2) 
                                                  (no associativity, at level 70).
  Notation "k |~ t1 →* t2" := (clos_refl_trans_1n _ (reduce k) t1 t2) 
                                                  (no associativity, at level 70).


  Axiom dec_is_pfunction : forall {t k} {d d0 : decomp k}, 
                               dec t k d -> dec t k d0 -> d = d0.

End DET_RED_MINI_SEM.



Module DET_RED_SEM_Facts (R : DET_RED_MINI_SEM).

  Module RF := RED_LANG_Facts R.
  Import R RF.

  Lemma reduce_red : 
      forall {k1 k2} (c : context k1 k2) (r : redex k2) t,  k1 |~ d_red r c → t  ->
          exists t', contract r = Some t' /\ t = c[t'].

  Proof.
    intros k1 k2 c r t H.
    assert (G: ~dead_ckind k1) by (intro; eapply proper_death_trans; eauto).
    destruct H as [k' [c' [r' [t' [H0 [H1 H2]]]]]].
    
    assert (H3 : d_red r c = d_red r' c'). 
    { eapply dec_is_pfunction; solve [reflexivity | unfold dec; eauto]. }
    inversion H3; dep_subst.
    eauto.
  Qed.

End DET_RED_SEM_Facts.

