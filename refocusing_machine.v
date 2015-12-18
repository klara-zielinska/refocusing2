
(*** Signatures ***)

Require Import Relations.
Require Import Entropy.
Require Import reduction_semantics.
Require Import refocusing_semantics.
Require Import abstract_machine.



Module Type REF_EVAL_APPLY_MACHINE (R : RED_REF_SEM) <: ABSTRACT_MACHINE.

  Import R.
  Import ST.

  Notation ick := init_ckind.

  Definition term  := term.
  Definition value := value ick.

  Inductive conf : Set :=
  | c_eval  : term -> forall {k}, context ick k -> conf
  | c_apply : forall {k}, context ick k -> R.value k -> conf.
  Definition configuration := conf.

  Definition load t                    : configuration := c_eval t [.].
  Definition value_to_conf (v : value) : configuration := c_apply [.] v.
  Coercion value_to_conf : value >-> configuration.
  Definition final (c : configuration) : option value := 
      match c with
      | c_apply _ [.] v => Some v 
      | _  => None
      end.
  Definition decompile (c : configuration) : term :=
      match c with
      | c_eval t _ c  => c[t]
      | c_apply _ c v => c[v]
      end.


  Reserved Notation "c1 → c2" (no associativity, at level 70).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k} (c : context ick k) r t0,
               dec_term t k = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_val  : forall t {k} (c : context ick k) v,
      	       dec_term t k = in_val v ->
               c_eval t c → c_apply c v
  | t_term : forall t {k} (c : context ick k) {t0 ec},
               dec_term t k = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
  | t_cred : forall ec {k} (v : R.value (k+>ec)) (c : context ick k) r t,
               dec_context ec k v = in_red r -> contract r = Some t ->
               c_apply (ec=:c) v → c_eval t c
  | t_cval : forall ec {k} (v : R.value (k+>ec)) (c : context ick k) v0,
               dec_context ec k v = in_val v0 ->
               c_apply (ec=:c) v → c_apply c v0
  | t_cterm: forall ec {k} (v : R.value (k+>ec)) (c : context ick k) t ec0,
               dec_context ec k v = in_term t ec0 ->
               c_apply (ec=:c) v → c_eval t (ec0=:c)

  where "st1 → st2" := (trans st1 st2).
  Definition transition := trans.
  Hint Unfold transition.

  Notation "t1 →+ t2" := (clos_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).
  Notation "t1 →* t2" := (clos_refl_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).


  Definition next_conf (_ : entropy) st :=
      match st with
      | c_eval t k c  => 
            match dec_term t k with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | c_apply _ (ccons ec k c) v => 
            match dec_context ec k v with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | c_apply _ [.] v => 
            None
      end.

  Axioms
  (final_correct :                                                              forall c,
       final c <> None -> ~exists c', c → c')
  (trans_computable :                                                       forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2)
  (finals_are_vals :                                                          forall c v,
       final c = Some v <-> c = v).

End REF_EVAL_APPLY_MACHINE.




(*
Module Type REF_PUSH_ENTER_MACHINE (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                                       <: DET_ABSTRACT_MACHINE.

  Import R.
  Import PERS.ST.


  Definition term  := term.
  Definition value := value init_ckind.


  Inductive conf : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> conf
  | c_fin : forall {k}, R.value k                -> conf.
  Definition configuration := conf.

  Definition c_init t  := c_eval t [.](init_ckind).
  Definition c_final (v : value) := c_fin v.
  (*Definition final_of (st : configuration) : option value := 
      match st with 
      | c_fin k v => 
          match is_initial k with
          | left H => match H in _ = k return R.value k -> option value with
                      | eq_refl => fun v => Some v
                      end v
          | _      => None
          end
      | _ => None
      end.
  Axiom final_of_correct : forall c v, final_of c = Some v <-> c_final v = c.*)


  Reserved Notation "c1 → c2" (at level 40, no associativity).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = in_red r -> 
               contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : R.value k},
               dec_term t k = in_val v ->
               c_eval t [.](k) → c_fin v
  | t_cred : forall t ec {t0} {k1 k2} (c : context k1 k2) {v r},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_red r ->
               contract r = Some t0 ->
               c_eval t (ec=:c) → c_eval t0 c
  | t_crec : forall t ec {t0 ec0 k1 k2} (c : context k1 k2) {v},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_term t0 ec0 ->
               c_eval t (ec=:c) → c_eval t0 (ec0=:c)
  | t_rec  : forall t {t0 ec k1 k2} (c : context k1 k2),
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.
  Hint Unfold transition.

  Axiom final_correct : forall v st, ~ c_final v → st.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).
  Reserved Notation "c1 →* c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition next_conf st :=
      match st with
      | c_eval t _ k2 c  => 
            match dec_term t k2 with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => match c in context _ k2 
                              return R.value k2 -> option configuration with 
                          | [.]          => fun _ => Some (c_fin v)
                          | ccons ec k c => fun v => 
                                match dec_context ec k v with
                                | in_red r       => option_map (fun t' => c_eval t' c)
                                                               (contract r)
                                | in_term t' ec' => Some (c_eval t' (ec'=:c))
                                | _              => None
                                end
                          end v
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | _ => None
      end.


  Axiom next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

End REF_PUSH_ENTER_MACHINE.*)





(*** Functors ***)


Require Import Util.
Require Export reduction_strategy.




Module RefEvalApplyMachine (R : RED_REF_SEM) <: REF_EVAL_APPLY_MACHINE R.

  Import R.
  Import ST.

  Notation ick := init_ckind.


  Definition term  := term.
  Definition value := value ick.

  Inductive conf : Set :=
  | c_eval  : term -> forall {k}, context ick k -> conf
  | c_apply : forall {k}, context ick k -> R.value k -> conf.
  Definition configuration := conf.

  Definition load t                    : configuration := c_eval t [.].
  Definition value_to_conf (v : value) : configuration := c_apply [.] v.
  Coercion value_to_conf : value >-> configuration.
  Definition final (c : configuration) : option value := 
      match c with
      | c_apply _ [.] v => Some v 
      | _  => None
      end.
  Definition decompile (c : configuration) : term :=
      match c with
      | c_eval t _ c  => c[t]
      | c_apply _ c v => c[v]
      end.


  Reserved Notation "c1 → c2" (no associativity, at level 70).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k} (c : context ick k) r t0,
               dec_term t k = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_val  : forall t {k} (c : context ick k) v,
      	       dec_term t k = in_val v ->
               c_eval t c → c_apply c v
  | t_term : forall t {k} (c : context ick k) {t0 ec},
               dec_term t k = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
  | t_cred : forall ec {k} (v : R.value (k+>ec)) (c : context ick k) r t,
               dec_context ec k v = in_red r -> contract r = Some t ->
               c_apply (ec=:c) v → c_eval t c
  | t_cval : forall ec {k} (v : R.value (k+>ec)) (c : context ick k) v0,
               dec_context ec k v = in_val v0 ->
               c_apply (ec=:c) v → c_apply c v0
  | t_cterm: forall ec {k} (v : R.value (k+>ec)) (c : context ick k) t ec0,
               dec_context ec k v = in_term t ec0 ->
               c_apply (ec=:c) v → c_eval t (ec0=:c)

  where "st1 → st2" := (trans st1 st2).
  Definition transition := trans.
  Hint Unfold transition.

  Notation "t1 →+ t2" := (clos_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).
  Notation "t1 →* t2" := (clos_refl_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).


  Definition next_conf (_ : entropy) st :=
      match st with
      | c_eval t k c  => 
            match dec_term t k with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | c_apply _ (ccons ec k c) v => 
            match dec_context ec k v with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | c_apply _ [.] v => 
            None
      end.


  Lemma final_correct :                                                         forall c,
       final c <> None -> ~exists c', c → c'.

  Proof.
    intros c H [c' H0].
    inversion H0; subst;
        simpl in H;
    congruence.
  Qed.


  Lemma trans_computable :                                                  forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2.
  Proof.
    intros c1 c2; split; intro H.

  (* -> *) {
      destruct (draw_fin_correct 1 Fin.F1) as [ent _].
      destruct H;
          simpl;
          match goal with H : @eq (interm_dec _) _ _ |- _ => rewrite H end;
      solve 
      [ eauto 
      | rewrite H0; eauto].
  }

  (* <- *) {
      destruct H as [ent H].
      destruct c1; simpl in H.
      - remember (dec_term t k) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * inversion H; subst.
            eapply t_red; eauto.
          * inversion H.
        + inversion H; subst.
          apply t_term; auto.
        + inversion H; subst.
          apply t_val; auto.
        + inversion H.
      - destruct c; autof.
        remember (dec_context ec k2 v) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * inversion H; subst.
            eapply t_cred; eauto.
          * inversion H.
        + inversion H; subst.
          apply t_cterm; auto.
        + inversion H; subst.
          apply t_cval; auto.
        + inversion H.
  }
  Qed.


  Lemma finals_are_vals :                                                     forall c v,
       final c = Some v <-> c = v.
  Proof.
    intros c v.
    destruct c; simpl.
    - intuition.
    - destruct c.
      + split; intro H;
            inversion H; dep_subst;
        solve [auto].
      + intuition.
  Qed.

End RefEvalApplyMachine.




(*Module RefPushEnterMachine (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                                 <: REF_PUSH_ENTER_MACHINE R PERS.

  Import R.
  Import PERS.ST.


  Definition term  := term.
  Definition value := value init_ckind.


  Inductive conf : Set :=
  | c_eval : term -> forall {k1 k2}, context k1 k2 -> conf
  | c_fin  : forall {k}, R.value k                 -> conf.
  Definition configuration := conf.

  Definition c_init t            := c_eval t [.](init_ckind).
  Definition c_final (v : value) := c_fin v.


  Reserved Notation "c1 → c2" (at level 40, no associativity).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = in_red r -> 
               contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : R.value k},
               dec_term t k = in_val v ->
               c_eval t [.](k) → c_fin v
  | t_cred : forall t ec {t0} {k1 k2} (c : context k1 k2) {v r},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_red r ->
               contract r = Some t0 ->
               c_eval t (ec=:c) → c_eval t0 c
  | t_crec : forall t ec {t0 ec0 k1 k2} (c : context k1 k2) {v},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_term t0 ec0 ->
               c_eval t (ec=:c) → c_eval t0 (ec0=:c)
  | t_rec  : forall t {t0 ec k1 k2} (c : context k1 k2),
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.
  Hint Unfold transition.


  Lemma final_correct : forall v st, ~ c_final v → st.
  Proof. inversion 1. Qed.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).
  Reserved Notation "c1 →* c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).


  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition next_conf st :=
      match st with
      | c_eval t _ k2 c  => 
            match dec_term t k2 with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => match c in context _ k2 
                              return R.value k2 -> option configuration with 
                          | [.]          => fun _ => Some (c_fin v)
                          | ccons ec k c => fun v => 
                                match dec_context ec k v with
                                | in_red r       => option_map (fun t' => c_eval t' c)
                                                               (contract r)
                                | in_term t' ec' => Some (c_eval t' (ec'=:c))
                                | _              => None
                                end
                          end v
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | _ => None
      end.


  Lemma next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

  Proof.
    intros c1 c2; split; intro H.

  (* -> *) {
      destruct c1; simpl in H.
      - remember (dec_term t k2) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * inversion H; subst.
            eapply t_red; eauto.
          * inversion H.
        + inversion H; subst.
          apply t_rec; auto.
        + destruct c.
          * inversion H; subst.
            apply t_cval; auto.
          * remember (dec_context ec k2 v) as dc.
            destruct dc;
            inversion H.
            { remember (contract r) as opt.
              destruct opt;
              inversion H; subst.
              eapply t_cred; eauto. }
            { eapply t_crec; eauto. }
        + inversion H.
      - inversion H. 
  }

  (* <- *) {
      destruct H;
          simpl;
          match goal with H : @eq (interm_dec _) _ _ |- _ => rewrite H end;
      try solve 
      [ auto 
      | rewrite H0; try rewrite H1; auto].
  }
  Qed.

End RefPushEnterMachine.*)
