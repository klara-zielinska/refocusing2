Require Export Wellfounded.Transitive_Closure.
Require Export Relations.
Require Export Relation_Operators.
Require Export List.
Require Import Setoid.

Ltac isda := intros; simpl in *; try discriminate; auto.

Section tcl.

Variable A : Type.
Variable R : relation A.

Notation trans_clos := (clos_trans A R).
Notation trans_clos_l := (clos_trans_1n A R).
Notation trans_clos_r := (clos_trans_n1 A R).

Lemma exl : forall x y, trans_clos x y -> R x y \/ exists z, R x z /\ trans_clos z y.
Proof with auto.
  induction 1.
  left...
  right; clear IHclos_trans2; destruct IHclos_trans1 as [H1 | [u [H1 H2]]].
  exists y...
  exists u; split; [ assumption | econstructor 2; eauto].
Qed.

Lemma exr : forall x y, trans_clos x y -> R x y \/ exists z, R z y /\ trans_clos x z.
Proof with auto.
  induction 1.
  left...
  right; clear IHclos_trans1; destruct IHclos_trans2 as [H1 | [u [H1 H2]]].
  exists y...
  exists u; split; [ assumption | econstructor 2; eauto].
Qed.

Lemma tcl_l_h : forall x y z, trans_clos x y -> trans_clos_l y z -> trans_clos_l x z.
Proof with eauto.
  induction 1; intros...
  econstructor 2...
Qed.

Lemma tcl_l : forall x y, trans_clos x y <-> trans_clos_l x y.
Proof with eauto.
  split; induction 1; intros...
  constructor...
  eapply tcl_l_h...
  constructor...
  econstructor 2...
  constructor...
Qed.

Lemma tcl_r_h : forall x y z, trans_clos y z -> trans_clos_r x y -> trans_clos_r x z.
Proof with eauto.
  induction 1; intros...
  econstructor 2...
Qed.

Lemma tcl_r : forall x y, trans_clos x y <-> trans_clos_r x y.
Proof with eauto.
  split; induction 1; intros.
  constructor...
  eapply tcl_r_h...
  constructor...
  econstructor 2...
  constructor...
Qed.

Lemma Acc_tcl_l : forall x, Acc trans_clos x -> Acc trans_clos_l x.
Proof with auto.
  induction 1.
  constructor; intros.
  apply H0; rewrite tcl_l...
Qed.

Theorem wf_clos_trans_l : well_founded R -> well_founded trans_clos_l.
Proof with auto.
  intros H a; apply Acc_tcl_l; apply wf_clos_trans...
Qed.

Lemma Acc_tcl_r : forall x, Acc trans_clos x -> Acc trans_clos_r x.
Proof with auto.
  induction 1.
  constructor; intros.
  apply H0; rewrite tcl_r...
Qed.

Theorem wf_clos_trans_r : well_founded R -> well_founded trans_clos_r.
Proof with auto.
  intros H a; apply Acc_tcl_r; apply wf_clos_trans...
Qed.

End tcl.

Definition opt_to_list {T} (o : option T) : list T :=
  match o with
  | None => nil
  | Some x => x :: nil
  end.

Section map_injective.

  Variables A B : Set.
  Variable f : A -> B.
  Hypothesis f_injective : forall a a0 : A, f a = f a0 -> a = a0.

  Lemma map_injective : forall l l0, map f l = map f l0 -> l = l0.
  Proof.
    induction l; destruct l0; intro H; inversion H; f_equal; auto.
  Qed.

End map_injective.

Section streams.

  Variable A : Set.

  CoInductive stream :=
  | s_nil : stream
  | s_cons : A -> stream -> stream.

  CoInductive bisim_stream : stream -> stream -> Prop :=
  | b_nil : bisim_stream s_nil s_nil
  | b_cons : forall (x : A) (s0 s1 : stream), bisim_stream s0 s1 -> bisim_stream (s_cons x s0) (s_cons x s1).

End streams.

Implicit Arguments s_nil [A].
Implicit Arguments s_cons [A].
Implicit Arguments bisim_stream [A].
Implicit Arguments b_nil [A].
Implicit Arguments b_cons [A x s0 s1].



Require Export List.
Require Import Program.
(*Require Export Util.*)

Module Type RED_LANG.

  (** The languages of terms, values, redex, and context, the empty context is also needed. *)
  Parameters term ckind : Set. 
  Parameters normal redex elem_context : ckind -> Set.
  Parameter  ckind_trans : forall k, elem_context k -> ckind.
  Parameter  init_ckind : ckind.
  Inductive context : ckind -> ckind -> Set :=
  | empty : forall k, context k k
  | ccons : forall {k1} (ec : elem_context k1) {k2}, context k2 k1 -> context k2 (ckind_trans k1 ec).

  (** The values and redexes are sublanguages of terms *)
  Parameter normal_to_term : forall {k}, normal k -> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Axiom normal_to_term_injective : forall k (v v' : normal k),
    normal_to_term v = normal_to_term v' -> v = v'.
  Axiom redex_to_term_injective : forall k (r r' : redex k),
    redex_to_term r = redex_to_term r' -> r = r'.

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context k1' k2' return context k3 k1' -> context k3 k2' with
      | empty _ => fun c1' => c1'
      | ccons _ ec _ c0' => fun c1' => ccons ec (compose c0' c1')
      end c1.
  Parameter atom_plug : term -> forall {k}, elem_context k -> term.
  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term := match c with
  | empty _ => t | ccons _ ec _ c' => plug (atom_plug t ec) c' end.
    

  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Parameter contract : forall {k}, redex k -> option term.

  Definition only_empty (t : term) (k : ckind) : Prop := 
    forall t' k' (c : context k k'), plug t' c = t -> c ~= empty.
  Definition only_trivial (t : term) (k : ckind) : Prop := 
    forall t' k' (c : context k k'), plug t' c = t -> 
      c ~= empty \/ exists (v : normal k'), t' = normal_to_term v.

  Axiom value_trivial : forall k (v : normal k), only_trivial (normal_to_term v) k.
  Axiom redex_trivial : forall k (r : redex k), only_trivial (redex_to_term r) k.
  Axiom value_redex : forall k (v : normal k) (r : redex k), normal_to_term v <> redex_to_term r.
  Axiom trivial_val_red : forall k (t : term), only_trivial t k ->
    (exists (v : normal k), t = normal_to_term v) \/ (exists (r : redex k), t = redex_to_term r).

  (** Datatype of decompositions -- either a value or a redex in a context (analogous to the decompose lemma) *)
  Inductive decomp k : Set :=
  | d_val : normal k -> decomp k
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k.

  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Inductive interm_dec k : Set :=
  | in_red  : redex k  -> interm_dec k
  | in_val  : normal k -> interm_dec k
  | in_term : term -> elem_context k -> interm_dec k.

  Arguments in_red {k} _. Arguments in_val {k} _. Arguments in_term {k} _ _.

  Definition decomp_to_term {k} (d : decomp k) : term :=
  match d with
    | d_val v => normal_to_term v
    | d_red _ r c0 => plug (redex_to_term r) c0
  end.

End RED_LANG.

Module Type LANG_PROP (R : RED_LANG).

  Axiom plug_empty : forall t k, R.plug t (R.empty k) = t.
  Axiom compose_empty : forall {k1 k2} (c : R.context k1 k2), c = R.compose c (R.empty _).
  Axiom plug_compose : forall k1 k2 (c0 : R.context k1 k2) 
                                 k3 (c1 : R.context k3 k1) (t : R.term), 
                           R.plug t (R.compose c0 c1) = R.plug (R.plug t c0) c1.

End LANG_PROP.

Module Type RED_REF_LANG.

  Declare Module R : RED_LANG.

  Parameter dec_term    : R.term -> forall k, R.interm_dec k.
  Parameter dec_context : 
    forall {k} (ec : R.elem_context k), 
                            R.normal (R.ckind_trans k ec) -> R.interm_dec k.

  Inductive subterm_one_step : R.term -> R.term -> Prop :=
  | st_1 : forall t t0 {k} (ec : R.elem_context k),
               t = R.atom_plug t0 ec -> subterm_one_step t0 t.
  Axiom wf_st1 : well_founded subterm_one_step.

  Definition subterm_order := clos_trans_n1 R.term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

  Parameter ec_order : forall {k}, R.elem_context k -> R.elem_context k -> Prop.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Axiom wf_eco : forall {k}, well_founded (@ec_order k).

  Axiom dec_term_red_empty  : forall t k (r : R.redex k), 
                                  dec_term t k = R.in_red r -> R.only_empty t k.
  Axiom dec_term_val_empty  : forall t k (v : R.normal k), 
                                  dec_term t k = R.in_val v -> R.only_empty t k.
  Axiom dec_term_term_top   : forall t t' k (ec : R.elem_context k), 
            dec_term t k = R.in_term t' ec -> forall ec', ~ec <: ec'.
  Axiom dec_context_red_bot : forall k ec v r, 
            @dec_context k ec v = @R.in_red k r -> forall ec', ~ ec' <: ec.
  Axiom dec_context_val_bot : forall k ec v v', 
            @dec_context k ec v = @R.in_val k v' -> forall ec', ~ ec' <: ec.
  Axiom dec_context_term_next : 
    forall k ec v t ec', @dec_context k ec v = @R.in_term k t ec' -> 
        ec' <: ec /\ forall ec'', ec'' <: ec -> ~ ec' <: ec''.

  Axiom dec_term_correct : forall k t, match dec_term t k with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.normal_to_term v = t
    | R.in_term t' ec => R.atom_plug t' ec = t
    end.
  Axiom dec_context_correct : forall k ec v, match @dec_context k ec v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) ec
    | R.in_val v' => R.normal_to_term v' = R.atom_plug (R.normal_to_term v) ec
    | R.in_term t ec' => R.atom_plug t ec' = R.atom_plug (R.normal_to_term v) ec
    end.

  Axiom ec_order_antisym : forall k (ec ec0 : R.elem_context k), ec <: ec0 -> ~ ec0 <: ec.
  Axiom dec_ec_ord : forall t0 t1 k ec0 ec1, 
      @R.atom_plug t0 k ec0 = @R.atom_plug t1 k ec1 -> 
      ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Axiom elem_context_det : forall t0 t1 k ec0 ec1, 
    ec0 <: ec1 -> @R.atom_plug t0 k ec0 = @R.atom_plug t1 k ec1 ->
    exists v, t1 = @R.normal_to_term (R.ckind_trans k ec1) v.

End RED_REF_LANG.

  Ltac prove_st_wf := intro a; constructor; induction a; (intros y H; 
    inversion H as [t t0 ec DECT]; subst; destruct ec; inversion DECT; subst; constructor; auto).
  Ltac prove_ec_wf := intro a; destruct a; repeat (constructor; intros ec T; destruct ec; inversion T; subst; clear T).

Module Type ABSTRACT_MACHINE.

  Parameters term configuration : Set.
  Parameter normal : Set.
  Parameter c_init : term -> configuration.
  Parameter c_final : normal -> configuration.
  Parameter transition : configuration -> configuration -> Prop.

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

  Inductive eval : term -> normal -> Prop :=
  | e_intro : forall (t : term) (v : normal), trans_close (c_init t) (c_final v) -> eval t v.

End ABSTRACT_MACHINE.

Module Type SOS_SEM.

  Parameters term normal : Set.
  Parameter step : term -> term -> Prop.
  Parameter value_to_term : normal -> term.

  Inductive step_close : term -> normal -> Prop :=
  | s_val  : forall v, step_close (value_to_term v) v
  | s_step : forall t t0 v, step t t0 -> step_close t0 v -> step_close t v.

End SOS_SEM.


Module Type RED_SEM (R : RED_LANG).

  Parameter dec : R.term -> forall {k1 k2}, R.context k1 k2 -> R.decomp k1 -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall k1 (r : R.redex k1) k2 (c : R.context k2 k1), 
                             dec (R.redex_to_term r) c (R.d_red r c).

  Axiom decompose : forall (t : R.term) (k : R.ckind), 
      (exists (v : R.normal k), t = R.normal_to_term v) \/
      (exists k' (r : R.redex k') (c : R.context k k'), R.plug (R.redex_to_term r) c = t).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall t {k1 k2} (c : R.context k1 k2) d, dec t c d -> 
      R.decomp_to_term d = R.plug t c.

  Axiom dec_plug : forall k1 k2 (c : R.context k1 k2) k3 (c0 : R.context k3 k1) t d, 
                       dec (R.plug t c) c0 d -> dec t (R.compose c c0) d.
  Axiom dec_plug_rev : forall k1 k2 (c : R.context k1 k2) k3 (c0 : R.context k3 k1) t d, 
                           dec t (R.compose c c0) d -> dec (R.plug t c) c0 d.

  Inductive decempty : R.term -> forall {k}, R.decomp k -> Prop :=
  | d_intro : forall (t : R.term) k (d : R.decomp k), dec t (R.empty _) d -> decempty t d.

  Inductive iter : forall {k}, R.decomp k -> R.normal k -> Prop :=
  | i_val : forall {k} (v : R.normal k), iter (R.d_val v) v
  | i_red : forall {k} (r : R.redex k) t {k'} (c : R.context k' k) d v,
              R.contract r = Some t -> decempty (R.plug t c) d -> iter d v ->
              iter (R.d_red r c) v.

  Inductive eval : R.term -> forall k, R.normal k -> Prop :=
  | e_intro : forall t k d v, decempty t d -> iter d v -> eval t k v.

End RED_SEM.

Module Type RED_REF_SEM (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : R.term -> forall k, R.interm_dec k.
  Parameter dec_context : forall {k} (ec : R.elem_context k),
                              R.normal (R.ckind_trans k ec) -> R.interm_dec k.

  Axiom dec_term_correct : forall k t, match dec_term t k with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.normal_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val v0 => R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t ec0 => R.atom_plug t ec0 = R.atom_plug (R.normal_to_term v) c
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : R.term -> forall {k1 k2}, R.context k1 k2 -> R.decomp k1 -> Prop :=
  | d_dec  : forall (t : R.term) {k1 k2} (c : R.context k1 k2) (r : R.redex k2)
               (DT  : dec_term t k2 = R.in_red r),
               dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) {k1 k2} (c : R.context k1 k2) (v : R.normal k2) (d : R.decomp k1)
               (DT  : dec_term t k2 = R.in_val v)
               (R_C : decctx v c d),
               dec t c d
  | d_term : forall (t t0 : R.term) {k1 k2} (c : R.context k1 k2) (ec : R.elem_context k2) (d : R.decomp k1)
               (DT  : dec_term t k2 = R.in_term t0 ec)
               (R_T : dec t0 (R.ccons ec c) d),
               dec t c d
  with decctx : forall {k2}, R.normal k2 -> forall {k1}, R.context k1 k2 -> R.decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : R.normal k), decctx v (R.empty _) (R.d_val v)
  | dc_dec  : forall {k2} (ec : R.elem_context k2) v {k1} (c : R.context k1 k2) (r : R.redex k2),
                dec_context ec v = R.in_red r ->
                decctx v (R.ccons ec c) (R.d_red r c)
  | dc_val  : forall {k2} (v0 : R.normal k2) (ec : R.elem_context k2) v {k1} (c : R.context k1 k2) 
                         (d : R.decomp k1)
                (DC  : dec_context ec v = R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (R.ccons ec c) d
  | dc_term : forall {k2} (ec ec0 : R.elem_context k2) v {k1} (c : R.context k1 k2) (t : R.term) (d : R.decomp k1)
                (DC  : dec_context ec v = R.in_term t ec0)
                (R_T : dec t (R.ccons ec0 c) d),
                decctx v (R.ccons ec c) d.

  Axiom dec_val_self : forall k2 (v : R.normal k2) {k1} (c : R.context k1 k2) d, 
      dec (R.normal_to_term v) c d <-> decctx v c d.

  Declare Module RS : RED_SEM R with Definition dec := dec.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

End RED_REF_SEM.

Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module Red_Sem : RED_REF_SEM R.

  Axiom dec_context_not_val : forall k v0 (ec : R.elem_context k) v, 
            Red_Sem.dec_context ec v <> R.in_val v0. (* ??? *)
  Axiom dec_term_value : forall k v, Red_Sem.dec_term (R.normal_to_term v) k = R.in_val v.

End PE_REF_SEM.




Require Import Setoid.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.



Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Lemma plug_empty : forall t k, R.plug t (R.empty k) = t.
  Proof.
    intros; simpl; auto.
  Qed.
  Hint Resolve plug_empty : prop.

  Lemma compose_empty : forall k1 k2 (c : R.context k1 k2), c = R.compose c (R.empty _).
  Proof.
    intros. induction c. auto. simpl. rewrite<- IHc. auto.
  Qed.
  Hint Resolve compose_empty : prop.

  Lemma plug_compose : forall k1 k2 (c  : R.context k1 k2) k3 (c' : R.context k3 k1) (t : R.term), R.plug t (R.compose c c') = R.plug (R.plug t c) c'.
  Proof.
    intros ? ? ? ? ?. induction c; intro. auto. apply IHc.
  Qed.
  Hint Resolve plug_compose : prop.

End Lang_Prop.



(* reszta nie poprawiona *)



Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Definition dec_term := R.dec_term.
  Definition dec_context {k} := @R.dec_context k.
  Inductive dec : R.R.term -> forall {k}, R.R.context k -> R.R.decomp -> Prop :=
  | d_dec  : forall (t : R.R.term) {k} (c : R.R.context k) (r : R.R.redex k)
               (DT  : dec_term k t = R.R.in_red r),
               dec t c (R.R.d_red r c)
  | d_v    : forall (t : R.R.term) {k} (c : R.R.context k) (v : R.R.normal k) (d : R.R.decomp)
               (DT  : dec_term k t = R.R.in_val v)
               (R_C : decctx v c d),
               dec t c d
  | d_term : forall (t t0 : R.R.term) {k} (c : R.R.context k) (ec : R.R.elem_context k) 
                    (d : R.R.decomp)
               (DT  : dec_term k t = R.R.in_term t0 ec)
               (R_T : dec t0 (R.R.ccons ec c) d),
               dec t c d
  with decctx : forall {k}, R.R.normal k -> forall {k}, R.R.context k -> R.R.decomp -> Prop :=
  | dc_end  : forall (v : R.R.normal R.R.init_ckind), decctx v R.R.empty (R.R.d_val v)
  | dc_dec  : forall {k} (ec : R.R.elem_context k) v (c : R.R.context k) (r : R.R.redex k),
                dec_context ec v = R.R.in_red r ->
                decctx v (R.R.ccons ec c) (R.R.d_red r c)
  | dc_val  : forall {k} (v0 : R.R.normal k) (ec : R.R.elem_context k) v (c : R.R.context k) 
                         (d : R.R.decomp)
                (DC  : dec_context ec v = R.R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (R.R.ccons ec c) d
  | dc_term : forall {k} (ec ec0 : R.R.elem_context k) v (c : R.R.context k) 
                     (t : R.R.term) (d : R.R.decomp)
                (DC  : dec_context ec v = R.R.in_term t ec0)
                (R_T : dec t (R.R.ccons ec0 c) d),
                decctx v (R.R.ccons ec c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
    
  Notation " a <| b " := (R.subterm_order a b) (at level 40).
  Notation " a <: b " := (R.ec_order a b) (at level 40).

  Lemma sto_trans : forall t t0 t1, t <| t0 -> t0 <| t1 -> t <| t1.
  Proof with auto.
    induction 2;
    econstructor 2; eauto.
  Qed.


  Lemma plug_le_eq : forall k (c : R.R.context k) t t0, R.R.plug t0 c = t -> 
                         t0 <| t \/ (c ~= R.R.empty /\ t = t0).
  Proof with auto.
    intro k.
    induction c; intros.
    simpl in H; right; auto.
    left; simpl in H. subst. destruct (IHc (R.R.plug t0 c) t0); auto.
      apply tn1_trans with (y := R.R.plug t0 c). apply R.st_1 with (k:=k)(ec:=ec). auto.
      assumption.
      apply tn1_step. destruct H. rewrite H0. eapply R.st_1. reflexivity.
  Qed.
(*
  Lemma st_c : forall t0 t1, t0 <| t1 -> exists c, @R.R.plug t0 R.R.init_ckind c = t1.
  Proof with auto.
    intros t0 t1 H. induction H. inversion H; subst.
    exists (R.R.ccons ec R.R.empty); simpl; auto.
    destruct IHclos_trans_n1 as [c H1].
    exists (c ++ (existT _ k ec :: nil)); unfold R.R.plug in *; rewrite fold_left_app; simpl; subst; auto.
  Qed.
*)
  Definition value_one_step {k} (v v0 : R.R.normal k) : Prop := 
      R.subterm_one_step (R.R.normal_to_term v) (R.R.normal_to_term v0).
  Definition value_order k := clos_trans_n1 (R.R.normal k) value_one_step.
    
  Notation " a <v| b " := (value_order a b) (at level 40).
    
  Lemma wf_vo : forall {k}, well_founded (value_order k).
  Proof.
    intro k.
    apply wf_clos_trans_r. unfold value_one_step. apply wf_inverse_image. apply R.wf_st1.
  Qed.

(*    Reserved Notation " a <v| b " (at level 40).

    Inductive value_order : R.R.value -> R.R.value -> Prop :=
    | vc_1 : forall v0 v1 ec (ATOM: R.R.atom_plug (R.R.value_to_term v0) ec = (R.R.value_to_term v1)), v0 <v| v1
    | vc_m : forall v0 v1 v2 ec (REC: v0 <v| v1) (ATOM: R.R.atom_plug (R.R.value_to_term v1) ec = (R.R.value_to_term v2)), v0 <v| v2
    where " a <v| b " := (value_order a b).

    Definition hp (v v0 : R.R.value) := (R.R.value_to_term v) <| (R.R.value_to_term v0).

    Lemma wf_vo : well_founded value_order.
    Proof with auto.
      apply wf_incl with hp.
      unfold inclusion; intros; induction H; [ econstructor | econstructor 2]; eauto; econstructor; eauto.
      apply wf_inverse_image; apply R.wf_sto.
    Qed.*)

    Lemma dec_val : forall {k} (v : R.R.normal k) (c : R.R.context k) (d : R.R.decomp), dec (R.R.normal_to_term v) c d -> decctx v c d.
    Proof with eauto.
      intro k.
      induction v using (well_founded_ind wf_vo); intros.

      dependent destruction H0; unfold dec_term in *;
      assert (hh := R.dec_term_correct k (R.R.normal_to_term v)); rewrite DT in hh.

      symmetry in hh; contradiction (R.R.value_redex _ _ _ hh).

      rewrite<- (R.R.normal_to_term_injective _ _ _ hh).
      assumption.

      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate H1.
      destruct H1 as [v0 H1]; subst t.
      symmetry in hh; assert (ht := R.st_1 _ _ _ hh);
      apply (tn1_step _ value_one_step) in ht; change (v0 <v| v) in ht.
      inversion H0; subst; unfold dec_term in DT; rewrite DT in Heqi; inversion Heqi; subst.
      clear H0 Heqi DT; assert (H0 := H _ ht _ _ R_T); clear ht R_T.
      generalize dependent v0.
      induction ec using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context ec v0); assert (hc := R.dec_context_correct ec v0);
      destruct i; rewrite <- Heqi in hc; rewrite <- hh in hc.
      symmetry in hc; contradiction (R.R.value_redex _ _ hc).
      clear H H0; apply R.R.value_to_term_injective in hc; subst.
      inversion H1; subst; unfold dec_context in DC; rewrite DC in Heqi; inversion Heqi; subst; auto.
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate.
      destruct H2 as [v1 H2]; subst t.
      inversion H1; subst; unfold dec_context in DC; rewrite DC in Heqi; inversion Heqi; subst.
      clear Heqi H1.
      apply H0 with ec1 v1...
      destruct (R.dec_context_term_next _ _ _ _ DC)...
      apply H...
      repeat econstructor...
    Qed.

    Lemma val_dec : forall v c d, decctx v c d -> dec (R.R.value_to_term v) c d.
    Proof with eauto.
      induction v using (well_founded_ind wf_vo); intros.
      remember (R.dec_term (R.R.value_to_term v)); assert (hh := R.dec_term_correct (R.R.value_to_term v));
      destruct i; rewrite <- Heqi in hh.
      symmetry in hh; contradiction (R.R.value_redex _ _ hh).
      apply R.R.value_to_term_injective in hh; subst; econstructor...
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate H1.
      destruct H1 as [v0 H1]; subst t; econstructor 3...
      apply H; [ repeat econstructor | clear Heqi; generalize dependent v0]...
      induction e using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context e v0); assert (hc := R.dec_context_correct e v0);
      destruct i; rewrite <- Heqi in hc; rewrite hh in hc.
      symmetry in hc; contradiction (R.R.value_redex _ _ hc).
      clear H H1; apply R.R.value_to_term_injective in hc; subst; econstructor...
      destruct (R.R.value_trivial v t (e0 :: nil)); simpl...
      discriminate.
      destruct H2 as [v1 H2]; subst t; econstructor 4...
      apply H.
      repeat econstructor...
      apply H1...
      symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi)...
    Qed.

  Module RS : RED_SEM R.R with Definition dec := dec.
    Definition dec := dec.

    Lemma decompose : forall t : R.R.term, (exists v:R.R.value, t = R.R.value_to_term v) \/
      (exists r:R.R.redex, exists c:R.R.context, R.R.plug (R.R.redex_to_term r) c = t).
    Proof with eauto.
      induction t using (well_founded_ind R.wf_sto); intros.


      remember (R.dec_term t); assert (hh := R.dec_term_correct t); destruct i;
      rewrite <- Heqi in hh.
      right; exists r; exists R.R.empty...
      left; exists v...
      destruct (H t0) as [[v Hv] | [r [c Hrc]]].
      repeat econstructor...
      subst t0; clear Heqi; generalize dependent v; induction e using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context e v); assert (ht := R.dec_context_correct e v); destruct i;
      rewrite <- Heqi in ht; rewrite hh in ht.
      right; exists r; exists R.R.empty...
      left; exists v0...
      destruct (H t0) as [[v0 Hv] | [r [c Hrc]]].
      repeat econstructor...
      symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi) as [H1 _].
      subst t0; destruct (H0 e0 H1 v0 ht) as [[v1 Hv1] | [r [c Hrc]]].
      left; exists v1...
      right; exists r; exists c...
      right; exists r; exists (c ++ (e0 :: nil)); 
      subst t0; unfold R.R.plug in *; rewrite fold_left_app...
      right; exists r; exists (c ++ (e :: nil));
      subst t0; unfold R.R.plug in *; rewrite fold_left_app...
    Qed.

    Lemma dec_redex_self_e : forall (r : R.R.redex), dec (R.R.redex_to_term r) (R.R.empty) (R.R.d_red r R.R.empty).
    Proof with eauto.
      intros; remember (dec_term (R.R.redex_to_term r)); destruct i; unfold dec_term in Heqi;
      assert (hh := R.dec_term_correct (R.R.redex_to_term r)); rewrite <- Heqi in hh; simpl in hh.
      apply R.R.redex_to_term_injective in hh; subst; constructor...
      contradict hh;  apply R.R.value_redex.
      symmetry in Heqi; assert (H := R.dec_term_term_top _ _ _ Heqi).
      econstructor 3; simpl; eauto.
      destruct (R.R.redex_trivial r t (e :: R.R.empty) hh) as [H1 | [v H1]]; [ discriminate | subst t].
      clear H Heqi.
      generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context e v); assert (ht := R.dec_context_correct e v);
      rewrite <- Heqi in ht; destruct i; simpl in ht.
      rewrite hh in ht; apply R.R.redex_to_term_injective in ht; subst.
      constructor...
      rewrite <- ht in hh; contradiction (R.R.value_redex _ _ hh).
      econstructor 4; simpl; eauto.
      rewrite hh in ht; destruct (R.R.redex_trivial r t (e0 :: R.R.empty) ht) as [H4 | [v1 H4]].
      discriminate.
      subst t; symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi); apply H...
    Qed.

    Lemma dec_redex_self : forall (r : R.R.redex) (c : R.R.context), dec (R.R.redex_to_term r) c (R.R.d_red r c).
    Proof with eauto.
      intros.
      assert (hh := dec_redex_self_e r).
      induction hh using dec_Ind with
      (P := fun t c0 d (H : dec t c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red r' c1 => dec t (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end)
      (P0:= fun v c0 d (H : decctx v c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red r' c1 => decctx v (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end); try destruct d; auto; 
      [ constructor | econstructor | econstructor 3 | constructor | econstructor | econstructor 4]...
    Qed.

    Lemma dec_correct : forall t c d, dec t c d -> R.R.decomp_to_term d = R.R.plug t c.    
    Proof.
      induction 1 using dec_Ind with
      (P := fun t c d (H:dec t c d) => R.R.decomp_to_term d = R.R.plug t c)
      (P0:= fun v c d (H:decctx v c d) => R.R.decomp_to_term d = R.R.plug (R.R.value_to_term v) c); 
      simpl; auto; match goal with
      | [ DT: (dec_term ?t = ?int) |- _ ] => unfold dec_term in DT; assert (hh := R.dec_term_correct t); rewrite DT in hh
      | [ DC: (dec_context ?ec ?v = ?int) |- _ ] => unfold dec_context in DC; assert (hh := R.dec_context_correct ec v); rewrite DC in hh
      end; try rewrite IHdec; rewrite <- hh; subst; auto.
    Qed.

    Lemma dec_plug_rev : forall c c0 t d, dec t (R.R.compose c c0) d -> dec (R.R.plug t c) c0 d.
    Proof with auto.
      induction c; intros; simpl; auto.
      apply IHc; clear IHc; remember (R.dec_term (R.R.atom_plug t a)); destruct i;
      assert (hh := R.dec_term_correct (R.R.atom_plug t a)); rewrite <- Heqi in hh.
      symmetry in Heqi; discriminate ( R.dec_term_red_empty _ _ Heqi t (a :: nil)); reflexivity.
      symmetry in Heqi; discriminate (R.dec_term_val_empty _ _ Heqi t (a :: nil))...
      destruct (R.dec_ec_ord t0 t e a hh) as [H0 | [H0 | [H0 H1]]]; try (subst; econstructor 3; eauto; fail).
      symmetry in Heqi; contradict (R.dec_term_term_top _ _ _ Heqi _ H0).
      symmetry in hh; destruct (R.elem_context_det _ _ _ _ H0 hh) as [v H1]; subst t0.
      econstructor 3; eauto.
      clear Heqi; generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context e v); destruct i; symmetry in Heqi;
      assert (ht := R.dec_context_correct e v); rewrite Heqi in ht.
      contradiction (R.dec_context_red_bot _ _ _ Heqi a).
      contradiction (R.dec_context_val_bot _ _ _ Heqi a).
      destruct (R.dec_context_term_next _ _ _ _ Heqi) as [H2 H3].
      econstructor 4; eauto; rewrite <- hh in ht.
      destruct (R.dec_ec_ord _ _ _ _ ht) as [H4 | [H4 | [H4 H5]]]; try (subst; auto; fail).
      contradiction (H3 a H1).
      symmetry in ht; clear H3; destruct (R.elem_context_det _ _ _ _ H4 ht) as [v0 H5]; subst t0.
      apply H0; auto.
    Qed.

    Lemma dec_plug : forall c c0 t d, dec (R.R.plug t c) c0 d -> dec t (R.R.compose c c0) d.
    Proof with auto.
      induction c; intros; simpl; auto.
      apply IHc in H; clear IHc; inversion H; subst; unfold dec_term in DT; clear H;
      assert (hh := R.dec_term_correct (R.R.atom_plug t a)); rewrite DT in hh.
      discriminate (R.dec_term_red_empty _ _ DT t (a :: nil)); reflexivity.
      symmetry in hh; discriminate (R.dec_term_val_empty _ _ DT t (a :: R.R.empty))...
      destruct (R.dec_ec_ord t1 t ec a hh) as [H2 | [H2 | [H2 H3]]].
      contradiction (R.dec_term_term_top _ _ _ DT a).
      symmetry in hh; destruct (R.elem_context_det _ _ _ _ H2 hh) as [v H3]; subst t1.
      clear DT; generalize dependent v; generalize dependent ec.
      induction ec using (well_founded_ind R.wf_eco); intros.
      assert (H0 := dec_val _ _ _ R_T); inversion H0; subst; clear R_T;
      assert (ht := R.dec_context_correct ec v); unfold dec_context in DC; rewrite DC in ht; simpl in ht.
      contradiction (R.dec_context_red_bot _ _ _ DC a).
      contradiction (R.dec_context_val_bot _ _ _ DC a).
      clear H0.
      rewrite <- hh in ht.
      destruct (R.dec_context_term_next _ _ _ _ DC).
      destruct (R.dec_ec_ord _ _ _ _ ht) as [hq | [hq | [hq hw]]].
      contradiction (H1 a).
      symmetry in ht; destruct (R.elem_context_det _ _ _ _ hq ht) as [v1 h4]; subst t0.
      apply H with ec1 v1; auto.
      subst; auto.
      subst; auto.
    Qed.

    Inductive decempty : R.R.term -> R.R.decomp -> Prop :=
    | d_intro : forall (t : R.R.term) (d : R.R.decomp), dec t R.R.empty d -> decempty t d.

    Inductive iter : R.R.decomp -> R.R.value -> Prop :=
    | i_val : forall (v : R.R.value), iter (R.R.d_val v) v
    | i_red : forall (r : R.R.redex) (t : R.R.term) (c : R.R.context) (d : R.R.decomp) (v : R.R.value),
                R.R.contract r = Some t -> decempty (R.R.plug t c) d -> iter d v -> iter (R.R.d_red r c) v.

    Inductive eval : R.R.term -> R.R.value -> Prop :=
    | e_intro : forall (t : R.R.term) (d : R.R.decomp) (v : R.R.value), decempty t d -> iter d v -> eval t v.

  End RS.

  Definition dec_term_correct := R.dec_term_correct.
  Definition dec_context_correct := R.dec_context_correct.

  Lemma dec_val_self : forall v c d, dec (R.R.value_to_term v) c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec]; auto.
  Qed.

End RedRefSem.



















Module Type RED_PROP (R : RED_LANG) (RS : RED_REF_SEM(R)).

  Axiom dec_is_function : forall t d d0, RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Axiom iter_is_function : forall d k v v0, @RS.RS.iter d k v -> @RS.RS.iter d k v0 -> v = v0.
  Axiom eval_is_function : forall t k v v0, @RS.RS.eval t k v -> @RS.RS.eval t k v0 -> v = v0.
  Axiom dec_correct : forall t {k} c d, @RS.RS.dec t k c d -> R.decomp_to_term d = R.plug t c.
  Axiom dec_total : forall t, exists d, RS.RS.decempty t d.
  Axiom unique_decomposition : forall t: R.term, (exists k (v:R.normal k), t = R.normal_to_term v) \/ 
      (exists k (r:R.redex k), exists c: R.context k, R.plug (R.redex_to_term r) c = t /\ 
	  forall (r0:R.redex k) c0, (R.plug (R.redex_to_term r0) c0 = t -> r=r0 /\ c= c0)).

End RED_PROP.

Module Type PRE_ABSTRACT_MACHINE (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : forall {k} (ec : R.elem_context k), R.normal (R.ckind_trans _ ec) -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red _ r => R.redex_to_term r = t
    | R.in_val _ v => R.normal_to_term v = t
    | R.in_term t0 _ c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red _ r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val _ v0 =>  R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t _ c0 => R.atom_plug t c0 = R.atom_plug (R.normal_to_term v) c
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : R.term -> forall {k}, R.context k -> R.decomp -> Prop :=
  | d_dec  : forall (t : R.term) {k} (c : R.context k) (r : R.redex k)
                 (DT  : dec_term t = R.in_red r),
                 dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) {k} (c : R.context k) (v : R.normal k) (d : R.decomp)
                 (DT  : dec_term t = R.in_val v)
                 (R_C : decctx v c d),
                 dec t c d
  | d_term : forall (t t0 : R.term) {k} (ec : R.elem_context k) (c : R.context k) (d : R.decomp)
                 (DT  : dec_term t = R.in_term t0 ec)
                 (R_T : dec t0 (R.ccons ec c) d),
                 dec t c d
  with decctx : forall {k}, R.normal k -> R.context k -> R.decomp -> Prop :=
  | dc_end  : forall (v : R.normal R.init_ckind), decctx v R.empty (R.d_val v)
  | dc_dec  : forall {k} (ec : R.elem_context k) (c : R.context k) (v : R.normal (R.ckind_trans k ec)) (r : R.redex k)
                (DC  : dec_context ec v = R.in_red r),
                decctx v (R.ccons ec c) (R.d_red r c)
  | dc_val  : forall {k} (v0 : R.normal k) (ec : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k) (d : R.decomp)
                (DC  : dec_context ec v = R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (R.ccons ec c) d
  | dc_term : forall {k} (ec0 ec : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k) (t : R.term) (d : R.decomp)
                (DC  : dec_context ec v = R.in_term t ec0)
                (R_T : dec t (R.ccons ec0 c) d),
                decctx v (R.ccons ec c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : R.decomp -> forall {k}, R.normal k -> Prop :=
  | i_val : forall {k} (v : R.normal k), iter (R.d_val v) v
  | i_red : forall {k} (r : R.redex k) (t : R.term) (c : R.context k) (d : R.decomp) (v : R.normal k)
              (CONTR  : R.contract r = Some t)
              (DEC    : dec t c d)
              (R_ITER : iter d v),
              iter (R.d_red r c) v.

  Inductive eval : R.term -> forall {k}, R.normal k -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) {k} (v : R.normal k)
                (DEC  : dec t R.empty d)
                (ITER : iter d v),
                eval t v.

End PRE_ABSTRACT_MACHINE.

Module Type STAGED_ABSTRACT_MACHINE (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : forall {k} (ec : R.elem_context k), R.normal (R.ckind_trans k ec) -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red _ r => R.redex_to_term r = t
    | R.in_val _ v => R.normal_to_term v = t
    | R.in_term t0 _ c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red _ r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val _ v0 =>  R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t _ c0 => R.atom_plug t c0 = R.atom_plug (R.normal_to_term v) c
  end.

  Inductive dec : R.term -> forall {k1}, R.context k1 -> forall {k2}, R.normal k2 -> Prop :=
  | d_dec  : forall (t : R.term) {k1} (c : R.context k1) (r : R.redex k1) {k2} (v : R.normal k2)
               (DT   : dec_term t = R.in_red r)
               (R_IT : iter (R.d_red r c) v),
               dec t c v
  | d_v    : forall (t : R.term) {k1} (c : R.context k1) (v : R.normal k1) {k2} (v0 : R.normal k2)
               (DT   : dec_term t = R.in_val v)
               (R_C  : decctx v c v0),
               dec t c v0
  | d_many : forall (t t0 : R.term) {k1} (ec : R.elem_context k1) (c : R.context k1) {k2} (v : R.normal k2)
               (DT   : dec_term t = R.in_term t0 ec)
               (R_T  : dec t0 (R.ccons ec c) v),
               dec t c v
  with decctx : forall {k1}, R.normal k1 -> R.context k1 -> forall {k2}, R.normal k2 -> Prop :=
  | dc_end  : forall (v v0 : R.normal R.init_ckind)
               (IT_V : iter (R.d_val v) v0),
               decctx v R.empty v0
  | dc_dec  : forall {k} (v0 : R.normal k) (ec : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k) (r : R.redex k)
               (DC   : dec_context ec v = R.in_red r)
               (R_IT : iter (R.d_red r c) v0),
               decctx v (R.ccons ec c) v0
  | dc_val  : forall {k1} (v0 : R.normal k1) (ec : R.elem_context k1) (v : R.normal (R.ckind_trans k1 ec)) (c : R.context k1) {k2} (v1 : R.normal k2)
               (DC   : dec_context ec v = R.in_val v0)
               (R_C  : decctx v0 c v1),
               decctx v (R.ccons ec c) v1
  | dc_term : forall {k1} (t : R.term) (ec ec0 : R.elem_context k1) (v0 : R.normal (R.ckind_trans k1 ec)) (c : R.context k1) {k2} (v : R.normal k2)
               (DC   : dec_context ec v0 = R.in_term t ec0)
               (R_T  : dec t (R.ccons ec0 c) v),
               decctx v0 (R.ccons ec c) v
  with iter : R.decomp -> forall {k}, R.normal k -> Prop :=
  | i_val : forall {k} (v : R.normal k), iter (R.d_val v) v
  | i_red : forall {k1} (r : R.redex k1) (c : R.context k1) (t : R.term) {k2} (v : R.normal k2)
               (CONTR: R.contract r = Some t)
               (R_T  : dec t c v),
               iter (R.d_red r c) v.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : R.term -> forall {k}, R.normal k -> Prop :=
  | e_intro : forall (t : R.term) {k} (v : R.normal k), dec t R.empty v -> eval t v.

End STAGED_ABSTRACT_MACHINE.

Module Type EVAL_APPLY_MACHINE (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : forall {k} (ec : R.elem_context k), R.normal (R.ckind_trans k ec) -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red _ r => R.redex_to_term r = t
    | R.in_val _ v => R.normal_to_term v = t
    | R.in_term t0 _ c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red _ r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val _ v0 =>  R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t _ c0 => R.atom_plug t c0 = R.atom_plug (R.normal_to_term v) c
  end.

  Inductive dec : R.term ->  forall {k1}, R.context k1 -> forall {k2}, R.normal k2 -> Prop :=
  | d_d_r  : forall (t t0 : R.term) {k1} (c : R.context k1) (r : R.redex k1) {k2} (v : R.normal k2)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0)
               (R_T   : dec t0 c v),
               dec t c v
  | d_v    : forall (t : R.term) {k1} (c : R.context k1) (v : R.normal k1) {k2} (v0 : R.normal k2)
               (DT    : dec_term t = R.in_val v)
               (R_C   : decctx v c v0),
               dec t c v0
  | d_term : forall (t t0 : R.term) {k1} (ec : R.elem_context k1) (c : R.context k1) {k2} (v : R.normal k2)
               (DT    : dec_term t = R.in_term t0 ec) 
               (R_T   : dec t0 (R.ccons ec c) v),
               dec t c v
  with decctx : forall {k1}, R.normal k1 -> R.context k1 -> forall {k2}, R.normal k2 -> Prop :=
  | dc_end : forall (v : R.normal R.init_ckind), decctx v R.empty v
  | dc_red : forall {k1} (ec : R.elem_context k1) (v : R.normal (R.ckind_trans k1 ec)) (c : R.context k1) (r : R.redex k1) (t : R.term) {k2} (v0 : R.normal k2)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t)
               (R_T   : dec t c v0),
               decctx v (R.ccons ec c) v0
  | dc_rec : forall {k1} (v0 : R.normal k1) (ec : R.elem_context k1) (v : R.normal (R.ckind_trans k1 ec)) (c : R.context k1) {k2} (v1 : R.normal k2)
               (DC    : dec_context ec v = R.in_val v0)
               (R_C   : decctx v0 c v1),
               decctx v (R.ccons ec c) v1
  | dc_trm : forall {k1} (v : R.normal k1) (ec ec0 : R.elem_context k1) (v : R.normal (R.ckind_trans k1 ec)) (c : R.context k1) (t : R.term) {k2} (v0 : R.normal k2)
               (DC    : dec_context ec v = R.in_term t ec0)
               (R_T   : dec t (R.ccons ec0 c) v0),
               decctx v (R.ccons ec c) v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : R.term -> forall {k}, R.normal k -> Prop :=
  | e_intro : forall (t : R.term) {k} (v : R.normal k), dec t R.empty v -> eval t v.

End EVAL_APPLY_MACHINE.

Module Type PROPER_EA_MACHINE (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : forall {k} (ec : R.elem_context k), R.normal (R.ckind_trans k ec) -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red _ r => R.redex_to_term r = t
    | R.in_val _ v => R.normal_to_term v = t
    | R.in_term t0 _ c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red _ r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val _ v0 =>  R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t _ c0 => R.atom_plug t c0 = R.atom_plug (R.normal_to_term v) c
  end.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> forall {k}, R.context k -> configuration
  | c_apply : forall {k}, R.context k -> R.normal k -> configuration
  | c_final : forall {k}, R.normal k -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).
  
  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term), transition (c_init t) (c_eval t R.empty)
  | t_red  : forall (t t0 : R.term) {k} (c : R.context k) (r : R.redex k)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0),
               (c_eval t c) → (c_eval t0 c)
  | t_val  : forall (t : R.term) {k} (v : R.normal k) (c : R.context k)
      	       (DT    : dec_term t = R.in_val v),
               (c_eval t c) → (c_apply c v)
  | t_term : forall {k} (t t0 : R.term) (ec : R.elem_context k) (c : R.context k)
               (DT    : dec_term t = R.in_term t0 ec),
               (c_eval t c) → (c_eval t0 (R.ccons ec c))
  | t_cfin : forall (v : R.normal R.init_ckind),
               (c_apply R.empty v) → (c_final v)
  | t_cred : forall {k} (t : R.term) (ec : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k) (r : R.redex k)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t),
               (c_apply (R.ccons ec c) v) → (c_eval t c)
  | t_cval : forall {k} (v0 : R.normal k) (ec : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k)
               (DC    : dec_context ec v = R.in_val v0),
               (c_apply (R.ccons ec c) v) → (c_apply c v0)
  | t_cterm: forall {k} (t : R.term) (ec ec0 : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k)
               (DC    : dec_context ec v = R.in_term t ec0),
               (c_apply (R.ccons ec c) v) → (c_eval t (R.ccons ec0 c))
  where " a → b " := (transition a b).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition ckind := R.ckind
    with Definition normal := R.normal
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := @c_final.

End PROPER_EA_MACHINE.

Module Type PUSH_ENTER_MACHINE (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : forall {k} (ec : R.elem_context k), R.normal (R.ckind_trans k ec) -> R.interm_dec.
  Axiom dec_term_value : forall k (v : R.normal k), dec_term (R.normal_to_term v) = R.in_val v.
  Axiom dec_context_not_val : forall k v0 ec v, ~(@dec_context k ec v = @R.in_val k v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red _ r => R.redex_to_term r = t
    | R.in_val _ v => R.normal_to_term v = t
    | R.in_term t0 _ c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red _ r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val _ v0 =>  R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t _ c0 => R.atom_plug t c0 = R.atom_plug (R.normal_to_term v) c
  end.

  Inductive dec : R.term -> forall {k1}, R.context k1 -> forall {k2}, R.normal k2 -> Prop :=
  | dec_r    : forall (t t0 : R.term) {k1} (c : R.context k1) (r : R.redex k1) {k2} (v : R.normal k2)
                 (DT    : dec_term t = R.in_red r)
                 (CONTR : R.contract r = Some t0)
                 (R_T   : dec t0 c v),
                 dec t c v
  | dec_val  : forall (t : R.term) (v : R.normal R.init_ckind)
                 (DT    : dec_term t = R.in_val v),
                 dec t R.empty v
  | dec_v_t  : forall (t t0 : R.term) {k1} (ec ec0 : R.elem_context k1) (c : R.context k1) (v : R.normal (R.ckind_trans k1 ec)) {k2} (v0 : R.normal k2)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_term t0 ec0)
                 (R_T   : dec t0 (R.ccons ec0 c) v0),
                 dec t (R.ccons ec c) v0
  | dec_red  : forall (t t0 : R.term) {k1} (ec : R.elem_context k1) (c : R.context k1) (v : R.normal (R.ckind_trans k1 ec)) (r : R.redex k1) {k2} (v0 : R.normal k2)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_red r)
                 (CONTR : R.contract r = Some t0)
                 (R_T   : dec t0 c v0),
                 dec t (R.ccons ec c) v0
  | dec_rec  : forall (t t0 : R.term) {k1} (ec : R.elem_context k1) (c : R.context k1) {k2} (v : R.normal k2)
                 (DT    : dec_term t = R.in_term t0 ec)
                 (R_T   : dec t0 (R.ccons ec c) v),
                 dec t c v.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : R.term -> forall {k}, R.normal k -> Prop :=
  | e_intro : forall (t : R.term) {k} (v : R.normal k), dec t R.empty v -> eval t v.

End PUSH_ENTER_MACHINE.


Module Type PROPER_PE_MACHINE (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : forall {k} (ec : R.elem_context k), R.normal (R.ckind_trans k ec) -> R.interm_dec.
  Axiom dec_term_value : forall k (v : R.normal k), dec_term (R.normal_to_term v) = R.in_val v.
  Axiom dec_context_not_val : forall k v0 ec v, ~(@dec_context k ec v = @R.in_val k v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red _ r => R.redex_to_term r = t
    | R.in_val _ v => R.normal_to_term v = t
    | R.in_term t0 _ c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall k c v, match @dec_context k c v with
    | R.in_red _ r => R.redex_to_term r = R.atom_plug (R.normal_to_term v) c
    | R.in_val _ v0 =>  R.normal_to_term v0 = R.atom_plug (R.normal_to_term v) c
    | R.in_term t _ c0 => R.atom_plug t c0 = R.atom_plug (R.normal_to_term v) c
  end.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> forall {k}, R.context k -> configuration
  | c_final : forall {k}, R.normal k -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term),
               c_init t → c_eval t R.empty
  | t_red  : forall (t t0 : R.term) {k} (c : R.context k) (r : R.redex k)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0),
               c_eval t c → c_eval t0 c
  | t_cval : forall (t : R.term) (v : R.normal R.init_ckind)
               (DT    : dec_term t = R.in_val v),
               c_eval t R.empty → c_final v
  | t_cred : forall (t t0 : R.term) {k} (ec : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k) (r : R.redex k)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t0),
               c_eval t (R.ccons ec c) → c_eval t0 c
  | t_crec : forall (t t0 : R.term) {k} (ec ec0 : R.elem_context k) (v : R.normal (R.ckind_trans k ec)) (c : R.context k)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_term t0 ec0),
               c_eval t (R.ccons ec c) → c_eval t0 (R.ccons ec0 c)
  | t_rec  : forall (t t0 : R.term) {k} (ec : R.elem_context k) (c : R.context k)
               (DT    : dec_term t = R.in_term t0 ec),
               c_eval t c → c_eval t0 (R.ccons ec c)
  where " a →  b " := (transition a b).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition ckind := R.ckind
    with Definition normal := R.normal
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := @c_final.

End PROPER_PE_MACHINE.


Require Import Setoid.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.


Module Red_Prop (R : RED_LANG) (RS : RED_REF_SEM(R)) : RED_PROP R RS.

  Module LP := Lang_Prop R.

  Lemma dec_is_function : forall t d d0, RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Proof.
    intros t d d0 DE DE0; inversion_clear DE; inversion_clear DE0.
    refine (RS.dec_Ind (fun t c d (H:RS.RS.dec t c d) => forall d0 (DEC : RS.RS.dec t c d0), d = d0)
    (fun c v d (H:RS.decctx c v d) => forall d0 (DCTX : RS.decctx c v d0),  d = d0)
    _ _ _ _ _ _ _ t R.empty d DEC d0 DEC0); intros; simpl; auto; try apply H; match goal with
    | [ RD : (RS.RS.dec ?t ?c ?d), DT : (RS.dec_term ?t = ?int) |- _ ] => inversion RD; rewrite DT0 in DT; inversion DT
    | [ RC : (RS.decctx ?v (?ec :: ?c) ?d), DC : (RS.dec_context ?ec ?v = ?int) |- _ ] => inversion RC; rewrite DC0 in DC; inversion DC
    | [ RC : (RS.decctx ?v R.empty ?d) |- _] => inversion RC
    end; subst; auto.
  Qed.
  Hint Resolve dec_is_function : prop.

  Lemma iter_is_function : forall d v v0, RS.RS.iter d v -> RS.RS.iter d v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    inversion H...
    inversion H0; subst; rewrite CONTR0 in CONTR; inversion CONTR; subst;
    apply IHiter; cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.

  Lemma eval_is_function : forall t v v0, RS.RS.eval t v -> RS.RS.eval t v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros; inversion H; subst; cutrewrite (d = d0) in ITER...
  Qed.

  Lemma dec_correct : forall t c d, RS.RS.dec t c d -> R.decomp_to_term d = R.plug t c.
  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun t c d (H:RS.RS.dec t c d) => R.decomp_to_term d = R.plug t c)
    (P0:= fun v c d (H:RS.decctx v c d) => R.decomp_to_term d = R.plug (R.value_to_term v) c); simpl; auto;
    try (assert (hh := RS.dec_term_correct t); rewrite DT in hh; simpl in hh; try rewrite IHdec; subst; auto);
    assert (hh := RS.dec_context_correct ec v); rewrite DC in hh; simpl in hh; try rewrite IHdec; try (contradiction hh); rewrite <- hh; auto.
  Qed.

  Lemma dec_total : forall t, exists d, RS.RS.decempty t d.
  Proof.
    intro t; destruct (RS.RS.decompose t) as [[v Hv] | [r [c Hp]]]; intros; subst t.
    exists (R.d_val v); constructor; rewrite RS.dec_val_self; constructor.
    exists (R.d_red r c); constructor; apply RS.RS.dec_plug_rev;
    rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
  Qed.

  Lemma unique_decomposition : forall t:R.term, (exists v:R.value, t = R.value_to_term v) \/ 
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t /\ 
	  forall (r0:R.redex) c0, (R.plug (R.redex_to_term r0) c0 = t -> r=r0 /\ c= c0)).
  Proof.
    intro t; destruct (RS.RS.decompose t) as [[v H] | [r [c H]]]; intros;
    [left; exists v | right; exists r; exists c]; auto; split; auto; intros.
    assert (RS.RS.decempty t (R.d_red r c)).
    constructor; rewrite <- H; apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
    assert (RS.RS.decempty t (R.d_red r0 c0)).
    constructor; rewrite <- H0; apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
    assert (hh := dec_is_function _ _ _ H1 H2); injection hh; intros; auto.
  Qed.

End Red_Prop.
(*
Module RefRedSem_SOS (R : RED_REF_LANG) <: SOS_SEM.

  Definition not_val (t : R.R.term) : Prop := forall v, R.R.value_to_term v <> t.

  Lemma not_triv_term_ec : forall t, ~R.only_trivial t -> exists t0, exists ec0, R.R.atom_plug t0 ec0 = t /\ not_val t0.
  Proof.
    intros; remember (R.dec_term t); destruct i; [contradict H | contradict H | idtac]; symmetry in Heqi.
    unfold R.only_trivial; intros; left; eapply R.dec_term_red_empty; eauto.
    unfold R.only_trivial; intros; left; assert (hh := R.dec_term_correct t); 
    rewrite Heqi in hh; subst t; eapply R.value_empty; simpl; eauto.
    
    assert (hh := R.dec_term_correct t); rewrite Heqi in hh; subst t.

    generalize dependent e; induction e using (well_founded_ind R.wf); intros.


  Definition dec_simpl (t : R.R.term) (H : not_val t) :
    {d : R.R.interm_dec | match d with
      | R.R.in_red r => R.R.redex_to_term r = t
      | R.R.in_val v => False
      | R.R.in_term t0 ec0 => R.R.atom_plug t0 ec0 = t /\ forall v, R.R.value_to_term v <> t0
    end}.
  Proof.
    intros t H; remember (R.dec_term t); destruct i; assert (hh := R.dec_term_correct t); rewrite <- Heqi in hh; simpl in *.
    constructor 1 with (R.R.in_red r);  auto.
    contradiction (H _ hh).
    clear Heqi; generalize dependent e; induction e using (well_founded_ind R.wf).
  *)


Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM (R)) <: PRE_ABSTRACT_MACHINE (R).

  Module LP := Lang_Prop R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term : R.term -> R.interm_dec := RS.dec_term.
  Definition dec_context : R.elem_context -> R.value -> R.interm_dec := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : R.term -> R.context -> R.decomp -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex)
                 (DT  : dec_term t = R.in_red r),
                 dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (d : R.decomp)
                 (DT  : dec_term t = R.in_val v)
                 (R_C : decctx v c d),
                 dec t c d
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                 (DT  : dec_term t = R.in_term t0 ec)
                 (R_T : dec t0 (ec :: c) d),
                 dec t c d
  with decctx : R.value -> R.context -> R.decomp -> Prop :=
  | dc_end  : forall (v : R.value), decctx v R.empty (R.d_val v)
  | dc_dec  : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
                (DC  : dec_context ec v = R.in_red r),
                decctx v (ec :: c) (R.d_red r c)
  | dc_val  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                (DC  : dec_context ec v = R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (ec :: c) d
  | dc_term : forall (v : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term) (d : R.decomp)
                (DC  : dec_context ec v = R.in_term t ec0)
                (R_T : dec t (ec0 :: c) d),
                decctx v (ec :: c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (t : R.term) (c : R.context) (d : R.decomp) (v : R.value)
              (CONTR  : R.contract r = Some t)
              (DEC    : dec t c d)
              (R_ITER : iter d v),
              iter (R.d_red r c) v.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) (v : R.value)
                (DEC  : dec t R.empty d)
                (ITER : iter d v),
                eval t v.

  Lemma dec_id_l : forall t c d, RS.RS.dec t c d -> dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t c d (H : RS.RS.dec t c d) => dec t c d)
    (P0:= fun v c d (H0 : RS.decctx v c d) => decctx v c d);
    [ constructor | econstructor 2 | econstructor 3 | constructor | econstructor 2 | econstructor | econstructor 4]...
  Qed.
  Hint Resolve dec_id_l.

  Lemma dec_id_r : forall t c d, dec t c d -> RS.RS.dec t c d.
  Proof with eauto.
    induction 1 using dec_Ind with 
    (P := fun t c d (H : dec t c d) => RS.RS.dec t c d)
    (P0:= fun v c d (H0 : decctx v c d) => RS.decctx v c d);
    [ constructor | econstructor 2 | econstructor 3 | constructor | econstructor | econstructor | econstructor 4]...
  Qed.
  Hint Resolve dec_id_r.

  Lemma iterRedPam : forall (d : R.decomp) (v : R.value), RS.RS.iter d v -> iter d v.
  Proof with auto.
    induction 1; [ constructor | constructor 2 with t d; auto;
    inversion_clear D_EM]; rewrite app_nil_end with (l:=c);
    apply dec_id_l; apply RS.RS.dec_plug...
  Qed.

  Lemma evalRedPam : forall (t : R.term) (v : R.value), RS.RS.eval t v -> eval t v.
  Proof with auto.
    intros t v H; inversion_clear H; constructor 1 with d; [inversion_clear D_EM | apply iterRedPam]...
  Qed.
  Hint Resolve evalRedPam.

  Lemma iterPamRed : forall (d : R.decomp) (v : R.value), iter d v -> RS.RS.iter d v.
  Proof with auto.
    induction 1; [constructor | constructor 2 with t d; auto; constructor];
    apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty...
  Qed.

  Lemma evalPamRed : forall (t : R.term) (v : R.value), eval t v -> RS.RS.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor 1 with d; [ constructor | apply iterPamRed]; auto.
  Qed.
  Hint Resolve evalPamRed.

  Theorem evalPam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    split...
  Qed.

End PreAbstractMachine.

Module StagedAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: STAGED_ABSTRACT_MACHINE R.

  Module PAM := PreAbstractMachine R RS.
  Module LP := Lang_Prop R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term : R.term -> R.interm_dec := RS.dec_term.
  Definition dec_context : R.elem_context -> R.value -> R.interm_dec := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex) (v : R.value)
               (DT   : dec_term t = R.in_red r)
               (R_IT : iter (R.d_red r c) v),
               dec t c v
  | d_v    : forall (t : R.term) (c : R.context) (v v0 : R.value)
               (DT   : dec_term t = R.in_val v)
               (R_C  : decctx v c v0),
               dec t c v0
  | d_many : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
               (DT   : dec_term t = R.in_term t0 ec)
               (R_T  : dec t0 (ec :: c) v),
               dec t c v
  with decctx : R.value -> R.context -> R.value -> Prop :=
  | dc_end  : forall (v v0 : R.value)
               (IT_V : iter (R.d_val v) v0),
               decctx v R.empty v0
  | dc_dec  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DC   : dec_context ec v = R.in_red r)
               (R_IT : iter (R.d_red r c) v0),
               decctx v (ec :: c) v0
  | dc_val  : forall (v v0 v1 : R.value) (ec : R.elem_context) (c : R.context)
               (DC   : dec_context ec v = R.in_val v0)
               (R_C  : decctx v0 c v1),
               decctx v (ec :: c) v1
  | dc_term : forall (v v0 : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context)
               (DC   : dec_context ec v = R.in_term t ec0)
               (R_T  : dec t (ec0 :: c) v0),
               decctx v (ec :: c) v0
  with iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (c : R.context) (t : R.term) (v : R.value)
               (CONTR: R.contract r = Some t)
               (R_T  : dec t c v),
               iter (R.d_red r c) v.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

  Lemma decPamSam : forall (t : R.term) (c : R.context) (d : R.decomp),
    PAM.dec t c d -> forall (v : R.value), iter d v -> dec t c v.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P := fun t c d (H:PAM.dec t c d) => forall v, iter d v -> dec t c v)
    (P0 := fun c v d (H:PAM.decctx c v d) => forall v', iter d v' -> decctx c v v');
    intros; simpl;
    [econstructor 1 | econstructor 2 | econstructor 3 | constructor | econstructor | econstructor 3 | econstructor 4]...
  Qed.
  Hint Resolve decPamSam.

  Lemma iterPamSam : forall (d : R.decomp) (v : R.value), PAM.iter d v -> iter d v.
  Proof with eauto.
    induction 1; [constructor | econstructor 2]...
  Qed.
  Hint Resolve iterPamSam.

  Lemma evalPamSam : forall (t : R.term) (v : R.value), PAM.eval t v -> eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor...
  Qed.
  Hint Resolve evalPamSam.

  Module P := Red_Prop R RS.

  Lemma decSamPam : forall (t : R.term) (c : R.context) (v : R.value),
    dec t c v -> forall (d : R.decomp), PAM.dec t c d -> PAM.iter d v.
  Proof with auto.
    induction 1 using dec_Ind with
    (P  := fun t c v (H:dec t c v) => forall d, PAM.dec t c d -> PAM.iter d v)
    (P0 := fun v c v' (H:decctx v c v') => forall d, PAM.decctx v c d -> PAM.iter d v')
    (P1 := fun d v (H:iter d v) => PAM.iter d v); intros; simpl.
    (* Case 1 *)
    change (PAM.dec_term t = R.in_red r) in DT;
    inversion H; rewrite DT0 in DT; inversion DT; subst...
    (* Case 2 *)
    apply IHdec; change (PAM.dec_term t = R.in_val v) in DT;
    inversion H; subst; rewrite DT0 in DT; inversion DT; subst...
    (* Case 3 *)
    apply IHdec; change (PAM.dec_term t = R.in_term t0 ec) in DT;
    inversion H0; subst; rewrite DT0 in DT; inversion DT; subst...
    (* Case 4 *)
    inversion H; subst...
    (* Case 5 *)
    change (PAM.dec_context ec v = R.in_red r) in DC;
    inversion H; subst; rewrite DC0 in DC; inversion DC; subst...
    (* Case 5 *)
    apply IHdec; clear IHdec; change (PAM.dec_context ec v = R.in_val v0) in DC;
    inversion H; rewrite DC0 in DC; inversion DC; subst...
    (* Case 6 *)
    apply IHdec; inversion H0; subst; change (PAM.dec_context ec v = R.in_term t ec0) in DC;
    rewrite DC0 in DC; inversion DC; subst...
    (* Case 5 *)
    constructor.
    (* Case 6 *)
    destruct(P.dec_total (R.plug t c)) as [d H0]; inversion_clear H0.
    apply RS.RS.dec_plug in DEC; rewrite <- LP.compose_empty in DEC;
    constructor 2 with t d...
  Qed.
  Hint Resolve decSamPam.

  Lemma evalSamPam : forall (t : R.term) (v : R.value), eval t v -> PAM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; destruct (P.dec_total t) as [d H]; inversion_clear H; econstructor...
  Qed.
  Hint Resolve evalSamPam.

  Theorem evalSam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros t v; rewrite PAM.evalPam; split; intros...
  Qed.

End StagedAbstractMachine.

Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: EVAL_APPLY_MACHINE R.

  Module SAM := StagedAbstractMachine R RS.

  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | d_d_r  : forall (t t0 : R.term) (c : R.context) (r : R.redex) (v : R.value)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0)
               (R_T   : dec t0 c v),
               dec t c v
  | d_v    : forall (t : R.term) (c : R.context) (v v0 : R.value)
               (DT    : dec_term t = R.in_val v)
               (R_C   : decctx v c v0),
               dec t c v0
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
               (DT    : dec_term t = R.in_term t0 ec) 
               (R_T   : dec t0 (ec :: c) v),
               dec t c v
  with decctx : R.value -> R.context -> R.value -> Prop :=
  | dc_end : forall (v : R.value), decctx v R.empty v
  | dc_red : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex) (t : R.term)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t)
               (R_T   : dec t c v0),
               decctx v (ec :: c) v0
  | dc_rec : forall (v v0 v1 : R.value) (ec : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_val v0)
               (R_C   : decctx v0 c v1),
               decctx v (ec :: c) v1
  | dc_trm : forall (v v0 : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term)
               (DC    : dec_context ec v = R.in_term t ec0)
               (R_T   : dec t (ec0 :: c) v0),
               decctx v (ec :: c) v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

  Lemma decSamEam : forall (t : R.term) (c : R.context) (v : R.value), SAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using SAM.dec_Ind with
    (P := fun t c v (H:SAM.dec t c v) => dec t c v)
    (P0:= fun c v v' (H:SAM.decctx c v v') => decctx c v v')
    (P1:= fun d v (H:SAM.iter d v) => match d with
                                        | R.d_val v' => decctx v R.empty v'
                                        | R.d_red r c => forall t : R.term,
                                                         R.contract r = Some t -> dec t c v
                                      end); simpl; intros.
    (* Case 1 *)
    inversion R_IT; subst; econstructor 1...
    (* Case 2 *)
    econstructor 2...
    (* Case 3 *)
    econstructor 3...
    (* Case 4 *)
    inversion IT_V; subst; constructor.
    (* Case 5 *)
    inversion_clear R_IT; econstructor 2...
    (* Case 6 *)
    econstructor 3...
    (* Case 7 *)
    econstructor 4...
    (* Case 8 *)
    constructor.
    (* Case 9 *)
    rewrite CONTR in H0; inversion H0; subst; auto.
  Qed.

  Lemma evalSamEam : forall (t : R.term) (v : R.value), SAM.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decSamEam; auto.
  Qed.
  Hint Resolve evalSamEam.

  Lemma decEamSam : forall (t : R.term) (c : R.context) (v : R.value), dec t c v -> SAM.dec t c v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun t c v (H:dec t c v) => SAM.dec t c v)
    (P0:= fun v c v' (H:decctx v c v') => SAM.decctx v c v'); intros; simpl.
    econstructor 1; try econstructor...
    econstructor 2...
    econstructor 3...
    repeat constructor.
    econstructor 2; try econstructor 2...
    econstructor 3...
    econstructor 4...
  Qed.

  Lemma evalEamSam : forall (t : R.term) (v : R.value), eval t v -> SAM.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.

  Theorem evalEam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros t v; rewrite SAM.evalSam; split...
  Qed.

End EvalApplyMachine.

Module ProperEAMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: PROPER_EA_MACHINE R.

  Module EAM := EvalApplyMachine R RS.

  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.
    
  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_apply : R.context -> R.value -> configuration
  | c_final : R.value -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).
  
  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term), transition (c_init t) (c_eval t R.empty)
  | t_red  : forall (t t0 : R.term) (c : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0),
               (c_eval t c) → (c_eval t0 c)
  | t_val  : forall (t : R.term) (v : R.value) (c : R.context)
      	       (DT    : dec_term t = R.in_val v),
               (c_eval t c) → (c_apply c v)
  | t_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_term t0 ec),
               (c_eval t c) → (c_eval t0 (ec :: c))
  | t_cfin : forall (v : R.value),
               (c_apply R.empty v) → (c_final v)
  | t_cred : forall (v : R.value) (t : R.term) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t),
               (c_apply (ec :: c) v) → (c_eval t c)
  | t_cval : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_val v0),
               (c_apply (ec :: c) v) → (c_apply c v0)
  | t_cterm: forall (v : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_term t ec0),
               (c_apply (ec :: c) v) → (c_eval t (ec0 :: c))
  where " a → b " := (transition a b).

  Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := R.term.
    Definition value := R.value.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).

  Lemma decEamTrans : forall (t:R.term) (c : R.context) (v:R.value), EAM.dec t c v -> (c_eval t c) →+ (c_final v).
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t c v (H:EAM.dec t c v) => (c_eval t c) →+ (c_final v))
    (P0:= fun v c v' (H:EAM.decctx v c v') =>  (c_apply c v) →+ (c_final v')); intros; simpl; auto;
    try (constructor; constructor; auto; fail); econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve decEamTrans.

  Lemma evalEamMachine : forall (t : R.term) (v : R.value), EAM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor; econstructor 2 with (c_eval t R.empty); auto; constructor.
  Qed.
  Hint Resolve evalEamMachine.

  Lemma transDecEam : forall (t : R.term) (c : R.context) (v : R.value), (c_eval t c) →+ (c_final v) -> EAM.dec t c v.
  Proof with eauto.
    intros t c v X.
    refine (AM.trans_close_ind
    (fun c c0 =>match c, c0 with
      | c_eval t c, c_final v => EAM.dec t c v
      | c_apply c v, c_final v0 => EAM.decctx v c v0
      | _, _ => True
    end)
    _ _ (c_eval t c) (c_final v) X); intros; auto.
    (* Case 1 *)
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2; subst; auto;
    inversion_clear H; constructor 1; auto.
    (* Case 2 *)
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto; intros; inversion H; subst.
    econstructor...
    econstructor 3...
    econstructor 2...
    econstructor...
    econstructor 4...
    econstructor 3...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecEam.

  Lemma evalMachineEam : forall (t : R.term) (v : R.value), AM.eval t v -> EAM.eval t v.
  Proof with auto.
    intros t v H; inversion_clear H; constructor; inversion_clear H0; inversion H; subst...
  Qed.
  Hint Resolve evalMachineEam.

  Theorem eval_apply_correct : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> AM.eval t v.
  Proof with auto.
    intros t v; rewrite EAM.evalEam; split...
  Qed.

End ProperEAMachine.

Module PushEnterMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PUSH_ENTER_MACHINE R.

  Module EAM := EvalApplyMachine R PRS.Red_Sem.
  Module PR := Red_Prop R PRS.Red_Sem.

  Definition dec_term := PRS.Red_Sem.dec_term.
  Definition dec_context := PRS.Red_Sem.dec_context.
  Definition dec_context_not_val := PRS.dec_context_not_val.
  Definition dec_context_correct := PRS.Red_Sem.dec_context_correct.
  Definition dec_term_correct := PRS.Red_Sem.dec_term_correct.
  Definition dec_term_value := PRS.dec_term_value.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | dec_r    : forall (t t0 : R.term) (c : R.context) (r : R.redex) (v : R.value)
                 (DT    : dec_term t = R.in_red r)
                 (CONTR : R.contract r = Some t0)
                 (R_T   : dec t0 c v),
                 dec t c v
  | dec_val  : forall (t : R.term) (v : R.value)
                 (DT    : dec_term t = R.in_val v),
                 dec t R.empty v
  | dec_v_t  : forall (t t0 : R.term) (ec ec0 : R.elem_context) (c : R.context) (v v0 : R.value)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_term t0 ec0)
                 (R_T   : dec t0 (ec0 :: c) v0),
                 dec t (ec :: c) v0
  | dec_red  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v v0 : R.value) (r : R.redex)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_red r)
                 (CONTR : R.contract r = Some t0)
                 (R_T   : dec t0 c v0),
                 dec t (ec :: c) v0
  | dec_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
                 (DT    : dec_term t = R.in_term t0 ec)
                 (R_T   : dec t0 (ec :: c) v),
                 dec t c v.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

  Lemma decEamPem : forall (t : R.term) (c : R.context) (v : R.value), EAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t c v (H:EAM.dec t c v) => dec t c v)
    (P0:= fun v c v0 (H:EAM.decctx v c v0) =>
      match c with
      | nil => dec (R.value_to_term v) R.empty v0
      | (ec :: c) => forall d : R.interm_dec, dec_context ec v = d ->
        match d with
        | R.in_red r => forall t : R.term, R.contract r = Some t -> dec t c v0
        | R.in_term t ec0 => dec t (ec0 :: c) v0
        | R.in_val v => False
        end
      end); intros; simpl.
    (* Case 1 *)
    econstructor...
    (* Case 2 *)
    inversion R_C; subst.
    (* Case 2.1 *)
    constructor...
    (* Case 2.2 *)
    econstructor 4...
    apply (IHdec (R.in_red r))...
    (* Case 2.3 *)
    contradict (dec_context_not_val _ _ _ DC).
    (* Case 2.4 *)
    econstructor 3...
    apply (IHdec (R.in_term t0 ec0))...
    (* Case 3 *)
    econstructor 5...
    (* Case 4 *)
    constructor; apply dec_term_value...
    (* Case 5 *)
    change (EAM.dec_context ec v = d) in H0; rewrite DC in H0; inversion H0;
    subst; simpl; intros.
    rewrite CONTR in H0; inversion H0; subst; auto.
    (* Case 7 *)
    contradict (dec_context_not_val _ _ _ DC).
    (* Case 8 *)
    change (EAM.dec_context ec v = d) in H0; rewrite DC in H0; subst; simpl...
  Qed.

  Lemma evalEamPem : forall (t : R.term) (v : R.value), EAM.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamPem; auto.
  Qed.
  Hint Resolve evalEamPem.

  Lemma decPemEam : forall (t : R.term) (c : R.context) (v : R.value), dec t c v -> EAM.dec t c v.
  Proof with eauto.
    induction 1; intros; simpl; auto.
    econstructor 1...
    econstructor 2... econstructor...
    econstructor 2... econstructor 4...
    econstructor 2... econstructor 2...
    econstructor 3...
  Qed.

  Lemma evalPemEam : forall (t : R.term) (v : R.value), eval t v -> EAM.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decPemEam; auto.
  Qed.
  Hint Resolve evalPemEam.

  Theorem evalPem : forall (t : R.term) (v : R.value), PRS.Red_Sem.RS.eval t v <-> eval t v.
  Proof.
    intros t v; rewrite EAM.evalEam; split; auto.
  Qed.

End PushEnterMachine.

Module ProperPEMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PROPER_PE_MACHINE R.

  Module PEM := PushEnterMachine R PRS.

  Definition dec_term := PRS.Red_Sem.dec_term.
  Definition dec_context := PRS.Red_Sem.dec_context.
  Definition dec_term_value := PEM.dec_term_value.
  Definition dec_context_not_val := PRS.dec_context_not_val.
  Definition dec_context_correct := PRS.Red_Sem.dec_context_correct.
  Definition dec_term_correct := PRS.Red_Sem.dec_term_correct.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_final : R.value -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term),
               c_init t → c_eval t R.empty
  | t_red  : forall (t t0 : R.term) (c : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0),
               c_eval t c → c_eval t0 c
  | t_cval : forall (t : R.term) (v : R.value)
               (DT    : dec_term t = R.in_val v),
               c_eval t R.empty → c_final v
  | t_cred : forall (t t0 : R.term) (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t0),
               c_eval t (ec :: c) → c_eval t0 c
  | t_crec : forall (t t0 : R.term) (v : R.value) (ec ec0 : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_term t0 ec0),
               c_eval t (ec :: c) → c_eval t0 (ec0 :: c)
  | t_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_term t0 ec),
               c_eval t c → c_eval t0 (ec :: c)
  where " a →  b " := (transition a b).

  Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := R.term.
    Definition value := R.value.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).

  Lemma decPemTrans : forall (t : R.term) (c : R.context) (v : R.value), PEM.dec t c v -> (c_eval t c) →+ (c_final v).
  Proof with eauto.
    induction 1; intros; simpl; try (constructor; constructor; auto; fail); econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve decPemTrans.

  Lemma evalPemMachine : forall (t : R.term) (v : R.value), PEM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor; econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve evalPemMachine.

  Lemma transDecPem : forall (t : R.term) (c : R.context) (v : R.value), (c_eval t c) →+ (c_final v) -> PEM.dec t c v.
  Proof with eauto.
    intros t c v X; refine (AM.trans_close_ind
    (fun c c0 => match c, c0 with
      | c_eval t c, c_final v => PEM.dec t c v
      | _, _ => True
    end) _ _ (c_eval t c) (c_final v) X); intros...
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2; subst; auto; inversion_clear H; econstructor 2...
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto; intros; inversion H; subst.
    econstructor...
    econstructor 4...
    econstructor 3...
    econstructor 5...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecPem.

  Lemma evalMachinePem : forall (t : R.term) (v : R.value), AM.eval t v -> PEM.eval t v.
  Proof.
    intros t v H; constructor; inversion_clear H; inversion H0; subst; inversion H; subst; auto.
  Qed.
  Hint Resolve evalMachinePem.

  Theorem push_enter_correct : forall (t : R.term) (v : R.value), PRS.Red_Sem.RS.eval t v <-> AM.eval t v.
  Proof.
    intros t v; rewrite (PEM.evalPem); split; auto.
  Qed.

End ProperPEMachine.

