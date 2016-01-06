


(*** Interface ***)

Require Import Program
               Relations
               Subset
               Entropy
               rewriting_system 
               reduction_languages_facts
               reduction_semantics
               reduction_strategy_facts
               refocusing_semantics 
               abstract_machine.





Module Type SLOPPY_REF_EVAL_APPLY_MACHINE (R : RED_REF_SEM) <: ABSTRACT_MACHINE.

  Import R ST.

  Notation ick := init_ckind.

  Definition term  := term.
  Definition value := value ick.


  Inductive conf : Type :=
  | c_eval  : term -> forall {k}, context init_ckind k -> conf
  | c_apply : forall {k}, context init_ckind k -> R.value k -> conf.
  Definition configuration := conf.


  Definition load t                    : configuration := c_eval t [.].
  Coercion value_to_conf (v : value)   : configuration := c_apply [.] v.
  (*Coercion value_to_conf : value >-> configuration.*)
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
  Definition alive_state (st : configuration) := 
      match st with 
      | c_eval _ k _  => ~dead_ckind k 
      | c_apply k _ _ => ~dead_ckind k
      end.


  Section S1.

  Local Reserved Notation "c1 → c2" (no associativity, at level 70).

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

  End S1.


  Definition next_conf0 (st : configuration) : option configuration :=
      match st with
      | c_eval t k c  => 
            match dec_term t k with
            | in_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v     => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead      => None
            end
      | c_apply _ (ccons ec k c) v => 
            match dec_context ec k v with
            | in_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v     => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead      => None
            end
      | c_apply _ [.] _ => 
            None
      end.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Definition next_conf (_ : entropy) := next_conf0.


  Axioms
  (final_correct :                                                              forall c,
       final c <> None -> ~exists c', c → c')
  (trans_computable :                                                       forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2)
  (finals_are_vals :                                                          forall c v,
       final c = Some v <-> c = v)

  (next_eval_alive :                                   forall st t k (c : context ick k),
      next_conf0 st = Some (c_eval t c) -> ~dead_ckind k)
  (next_apply_alive :                                  forall st k (c : context ick k) v,
      next_conf0 st = Some (c_apply c v) -> ~dead_ckind k).

End SLOPPY_REF_EVAL_APPLY_MACHINE.





Module Type REF_EVAL_APPLY_MACHINE (R : PRECISE_RED_REF_SEM) <: ABSTRACT_MACHINE.

  Import R ST.

  Declare Module RAW : SLOPPY_REF_EVAL_APPLY_MACHINE R.
  Export RAW.


  Notation ick         := init_ckind.
  Definition term      := term.
  Definition value     := RAW.value.
  Notation alive_state := RAW.alive_state.


  Instance alive_state_CompPred : CompPred _ alive_state.
      split. 
      intro st; destruct st; apply (is_satisfied (fun k => ~dead_ckind k) k).
  Defined.


  (*Inductive conf : Type :=
  | c_eval  : term -> forall {k}, context ick k -> (k ? alive_ckind) -> conf
  | c_apply : forall {k}, context ick k -> R.value k -> (k ? alive_ckind) -> conf.*)
  Definition configuration := {S? RAW.configuration | alive_state}.

  Coercion conf_to_raw (st : configuration) := ¹st.
      (*match st with
      | c_eval t _ c _  => RAW.c_eval t c
      | c_apply _ c v _ => RAW.c_apply c v
      end.*)
  Definition load t                    : configuration := 
      submember_by alive_state (RAW.c_eval t [.]) init_ckind_alive.
     (*c_eval t [.] (init_ckind_alive `as witness of alive_ckind).*)
  Definition value_to_conf (v : value) : configuration := 
     submember_by alive_state (RAW.c_apply [.] v) init_ckind_alive.
     (*`as witness of alive_ckind).*)
  Coercion value_to_conf : value >-> configuration.
  Definition final (c : configuration) : option value := RAW.final c. 
  Definition decompile (c : configuration) : term := RAW.decompile c.
  Definition transition (st1 st2 : configuration) := RAW.transition st1 st2.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Axiom next_conf_alive :                             forall st1 st2 : RAW.configuration,
      RAW.next_conf0 st1 = Some st2 -> alive_state st2.


  Definition next_conf0 (st : configuration) : option configuration :=

      match RAW.next_conf0 st 
      as sto return RAW.next_conf0 st = sto -> option configuration
      with
      | Some st' => fun H => Some (submember_by _ st' (next_conf_alive st st' H))
      | None     => fun _ => None
      end eq_refl.

      (*
      match RAW.next_conf0 st 
      as sto return RAW.next_conf0 st = sto -> option configuration
      with

      | Some (RAW.c_eval t k c) => fun H => Some 

            (c_eval t c  (RAW.next_eval_alive st t k c H 
                                `as witness of alive_ckind) )

      | Some (RAW.c_apply k c v) => fun H => Some 

            (c_apply c v (RAW.next_apply_alive st k c v H 
                                `as witness of alive_ckind) )

      | None                     => fun _ => None

      end eq_refl.*)


  Definition next_conf (_ : entropy) := next_conf0.


  Axioms
  (final_correct :                                                              forall c,
       final c <> None -> ~exists c', c → c')
  (trans_computable :                                                       forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2)
  (finals_are_vals :                                                          forall c v,
       final c = Some v <-> c = v).

End REF_EVAL_APPLY_MACHINE.



(*
Module Type REF_PUSH_ENTER_MACHINE (R : RED_PE_REF_SEM R) <: DET_ABSTRACT_MACHINE.

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





(*** Implementation ***)


Require Import Util.




Module SloppyRefEvalApplyMachine (R : RED_REF_SEM) <: SLOPPY_REF_EVAL_APPLY_MACHINE R.

  Module RF := RED_LANG_Facts R.
  Import R RF ST.


  Notation ick := init_ckind.


  Definition term  := term.
  Definition value := value ick.


  Inductive conf : Type :=
  | c_eval  : term -> forall {k}, context init_ckind k -> conf
  | c_apply : forall {k}, context init_ckind k -> R.value k -> conf.
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
  Definition alive_state (st : configuration) := 
      match st with 
      | c_eval _ k _  => ~dead_ckind k 
      | c_apply k _ _ => ~dead_ckind k
      end.


  Section S1.

  Local Reserved Notation "c1 → c2" (no associativity, at level 70).

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

  End S1.


  Definition next_conf0 (st : configuration) : option configuration :=
      match st with
      | c_eval t k c  => 
            match dec_term t k with
            | in_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v     => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead      => None
            end
      | c_apply _ (ccons ec k c) v => 
            match dec_context ec k v with
            | in_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v     => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead      => None
            end
      | c_apply _ [.] _ => 
            None
      end.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Definition next_conf (_ : entropy) := next_conf0.


  Lemma final_correct :                                                         forall c,
       final c <> None -> ~exists c', c → c'.

  Proof.
    intros c H [c' H0].
    inversion H0; subst;
        simpl in H;
    congruence.
  Qed.


  Lemma trans_computable0 :                                                 forall c1 c2,
       c1 → c2 <-> next_conf0 c1 = Some c2.

  Proof.
    intros c1 c2; split; intro H.

  (* -> *) {
      destruct H;
          simpl;
          match goal with H : @eq (interm_dec _) _ _ |- _ => rewrite H end;
      solve 
      [ eauto 
      | rewrite H0; eauto].
  }

  (* <- *) {
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


  Lemma trans_computable :                                                  forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2.

  Proof with auto.
    intuition.
    - destruct (draw_fin_correct 1 Fin.F1) as [ent _].
      exists ent.
      apply trans_computable0...
    - destruct H as [ent H].
      apply trans_computable0...
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


  Lemma next_eval_alive :                              forall st t k (c : context ick k),
      next_conf0 st = Some (c_eval t c) -> ~dead_ckind k.

  Proof.
    intros st t k c H.
    destruct st; unfold next_conf0 in H; simpl in H. 
    - remember (dec_term t0 k0); symmetry in Heqi; 
      destruct i; try discriminate.
      + destruct (contract r); inversion H; dep_subst.
        auto using (proper_death2 [.]).
      + inversion H; dep_subst.
        eauto using dec_term_next_alive.
    - destruct c0; try discriminate.
      remember (dec_context ec k2 v); symmetry in Heqi; destruct i; 
      try discriminate.
      + destruct (contract r); inversion H; dep_subst.
        auto using (proper_death2 [.]).
      + inversion H; dep_subst.
        eauto using dec_context_next_alive.
  Qed.


  Lemma next_apply_alive :                             forall st k (c : context ick k) v,
      next_conf0 st = Some (c_apply c v) -> ~dead_ckind k.

  Proof.
    intros st k c v H.
    destruct st; unfold next_conf0 in H; simpl in H. 
    - remember (dec_term t k0); symmetry in Heqi; destruct i; 
      try discriminate.
      + destruct (contract r); inversion H; dep_subst; auto.
      + inversion H; dep_subst.
        intro H.
        apply (dec_term_from_dead t k) in H.
        congruence.
    - destruct c0; try discriminate.
      remember (dec_context ec k2 v0); symmetry in Heqi; destruct i; 
      try discriminate.
      + destruct (contract r); discriminate.
      + inversion H; dep_subst.
        intro H.
        assert (H0 : dead_ckind (k+>ec)) by auto using death_propagation.
        apply (dec_context_from_dead ec k v0) in H0.
        congruence.
  Qed.

End SloppyRefEvalApplyMachine.





Module RefEvalApplyMachine (R : PRECISE_RED_REF_SEM) <: REF_EVAL_APPLY_MACHINE R.

  Module RF := RED_LANG_Facts R.
  Module SF := RED_STRATEGY_STEP_Facts R R.ST.
  Import R RF ST SF.


  Module RAW := SloppyRefEvalApplyMachine R.
  Export RAW.

  Notation ick := init_ckind.

  Definition term  := term.
  Definition value := RAW.value.
  Notation alive_state := RAW.alive_state.


  Instance alive_state_CompPred : CompPred _ alive_state.
      split. 
      intro st; destruct st; apply (is_satisfied (fun k => ~dead_ckind k) k).
  Defined.


  (*Inductive conf : Type :=
  | c_eval  : term -> forall {k}, context ick k -> (k ? alive_ckind) -> conf
  | c_apply : forall {k}, context ick k -> R.value k -> (k ? alive_ckind) -> conf.*)
  Definition configuration := {S? RAW.configuration | alive_state }.

  Coercion conf_to_raw (st : configuration) := ¹st.
      (*match st with
      | c_eval t _ c _  => RAW.c_eval t c
      | c_apply _ c v _ => RAW.c_apply c v
      end.*)
  Definition load t                    : configuration := 
      submember_by alive_state (RAW.c_eval t [.]) init_ckind_alive.
     (*c_eval t [.] (init_ckind_alive `as witness of alive_ckind).*)
  Definition value_to_conf (v : value) : configuration := 
     submember_by alive_state (RAW.c_apply [.] v) init_ckind_alive.
     (*`as witness of alive_ckind).*)
  Coercion value_to_conf : value >-> configuration.
  Definition final (c : configuration) : option value := RAW.final c. 
  Definition decompile (c : configuration) : term := RAW.decompile c.
  Definition transition (st1 st2 : configuration) := RAW.transition st1 st2.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Lemma next_conf_alive :                             forall st1 st2 : RAW.configuration,
      RAW.next_conf0 st1 = Some st2 -> alive_state st2.

  Proof.
    intros st1 st2 H.
    destruct st1 as [t k c | k [ | ec c] v], st2; 
    unfold RAW.next_conf0 in H; simpl in *;
    try discriminate;
    try match goal with
    | H : context [dec_term ?t ?k] |- _ =>
          remember (dec_term t k); symmetry in Heqi; 
          destruct i; try discriminate;
          [ destruct (contract r); inversion H; dep_subst;
            auto using (proper_death2 [.])
          | inversion H; dep_subst;
            eauto using dec_term_next_alive, dec_term_val_alive ]
    | H : context [dec_context ?ec ?k ?v] |- _ =>
          remember (dec_context ec k v); symmetry in Heqi; destruct i; 
          try discriminate;
          [ destruct (contract r); inversion H; dep_subst;
            auto using (proper_death2 [.])
          | inversion H; dep_subst;
            eauto using dec_context_next_alive, dec_context_val_alive ]
    end.
  Qed.


(*
  Notation ick     := init_ckind.
  Definition term  := term.
  Definition value := value ick.
  Definition alive_ckind k := ~dead_ckind k.


  Inductive conf : Type :=
  | c_eval  : term -> forall {k}, context ick k -> (k ? alive_ckind) -> conf
  | c_apply : forall {k}, context ick k -> R.value k -> (k ? alive_ckind) -> conf.
  Definition configuration := conf.

  Coercion conf_to_raw st :=
      match st with
      | c_eval t _ c _  => RAW.c_eval t c
      | c_apply _ c v _ => RAW.c_apply c v
      end.
  Definition load t                    : configuration := 
     c_eval t [.] (init_ckind_alive `as witness of alive_ckind).
  Definition value_to_conf (v : value) : configuration := 
     c_apply [.] v (init_ckind_alive `as witness of alive_ckind).
  Coercion value_to_conf : value >-> configuration.
  Definition final (c : configuration) : option value := RAW.final c.
  Definition decompile (c : configuration) : term := RAW.decompile c.

  Definition transition (st1 st2 : configuration) := RAW.transition st1 st2.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Definition next_conf0 (st : configuration) : option configuration :=

      match RAW.next_conf0 st 
      as sto return RAW.next_conf0 st = sto -> option configuration 
      with

      | Some (RAW.c_eval t k c) => fun H => Some 

            (c_eval t c  (RAW.next_eval_alive st t k c H 
                                `as witness of alive_ckind) )

      | Some (RAW.c_apply k c v) => fun H => Some 

            (c_apply c v (RAW.next_apply_alive st k c v H 
                                `as witness of alive_ckind) )

      | None                     => fun _ => None

      end eq_refl.


  Definition next_conf (_ : entropy) := next_conf0.
*)

  Definition next_conf0 (st : configuration) : option configuration :=

      match RAW.next_conf0 st 
      as sto return RAW.next_conf0 st = sto -> option configuration
      with
      | Some st' => fun H => Some (submember_by _ st' (next_conf_alive st st' H))
      | None     => fun _ => None
      end eq_refl.

      (*
      match RAW.next_conf0 st 
      as sto return RAW.next_conf0 st = sto -> option configuration
      with

      | Some (RAW.c_eval t k c) => fun H => Some 

            (c_eval t c  (RAW.next_eval_alive st t k c H 
                                `as witness of alive_ckind) )

      | Some (RAW.c_apply k c v) => fun H => Some 

            (c_apply c v (RAW.next_apply_alive st k c v H 
                                `as witness of alive_ckind) )

      | None                     => fun _ => None

      end eq_refl.
      *)


  Definition next_conf (_ : entropy) := next_conf0.


  Lemma final_correct :                                                         forall c,
      final c <> None -> ~exists c', c → c'.

  Proof.
    intros c H [c' H0].
    destruct c, c';
        compute in H0;
        inversion H0; dep_subst;
        compute in H;
    congruence.
  Qed.


  Lemma RAW_trans_computable0 :                           forall st1 st2 : configuration,
      st1 → st2 <-> RAW.next_conf0 st1 = Some (st2 : RAW.configuration).

  Proof.
    destruct st1, st2.
    apply RAW.trans_computable0.
  Qed.

(*
    intros st1 st2; split; intro H.

  (* -> *) {
      destruct st1, st2; compute in H; dependent destruction H; dep_subst;
          simpl;
          try match goal with H : @eq (interm_dec _) _ _ |- _ => rewrite H end;
      try solve 
      [ eauto 
      | rewrite H0; eauto].
  }

  (* <- *) {
      destruct st1; simpl in H.
      - remember (dec_term t k) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * destruct st2; inversion H; dep_subst.
            eapply RAW.t_red; eauto.
          * inversion H.
        + destruct st2; inversion H; dep_subst.
          apply RAW.t_term; auto.
        + destruct st2; inversion H; dep_subst.
          apply RAW.t_val; auto.
        + inversion H.
      - destruct c; autof.
        remember (dec_context ec k2 v) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * destruct st2; inversion H; dep_subst.
            eapply RAW.t_cred; eauto.
          * inversion H.
        + destruct st2; inversion H; dep_subst.
          apply RAW.t_cterm; auto.
        + destruct st2; inversion H; dep_subst.
          apply RAW.t_cval; auto.
        + inversion H.
  }
  Qed.*)


  Lemma trans_computable0 :                                                 forall c1 c2,
      c1 → c2 <-> next_conf0 c1 = Some c2.

  Proof. 
    intros c1 c2. 

    rewrite (RAW_trans_computable0 c1 c2).
    unfold next_conf0.
    generalize (eq_refl : RAW.next_conf0 c1 = RAW.next_conf0 c1) as H.
    intro H.
    set (RAW.next_conf0 c1) as sto in H at 2 |- * at 2.
    destruct sto.
    - destruct c as [t k c | k c v];
          rewrite H at 1; destruct c2;
          split; intro H0; 
          inversion H0; dep_subst;
      solve 
      [ repeat f_equal; apply (f_equal (submember _ _)); apply witness_unique ].
    - split; congruence.
  Qed.


  Lemma trans_computable :                                                  forall c1 c2,
      c1 → c2 <-> exists e, next_conf e c1 = Some c2.

  Proof with auto.
    intros c1 c2; split; intro H.
    - destruct entropy_exists as [e _].
      exists e.
      apply trans_computable0...
    - destruct H.
      apply trans_computable0...
  Qed.


  Lemma finals_are_vals :                                                    forall st v,
      final st = Some v <-> st = v.

  Proof.
    intros st v.
    destruct st as [[? ? ? | ? c ?] ?]; simpl.
    - intuition.
    - destruct c.
      + split; intro H;
            inversion H; dep_subst;
            unfold value_to_conf;
        solve [try apply (f_equal (submember _ _)); auto].
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
