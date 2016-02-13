Require Import Program
               Entropy
               Subset
               Util
               rewriting_system
               lam_no
               abstract_machine
               reduction_semantics
               reduction_languages_facts.




Module Lam_NO_HandDecProc.

  Module RF := RED_LANG_Facts Lam_NO_PreRefSem.
  Import Lam_NO_PreRefSem RF.



  Inductive dec_proc {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | d_VarC   : forall x (c : context k1 C) d,
                 decctx_proc (vCVar x) c d ->
                 dec_proc (Var x) c d 
  | d_VarECa : forall x (c : context k1 ECa) d,
                 decctx_proc (vECaVar x) c d ->
                 dec_proc (Var x) c d

  | d_LamC   : forall x t (c : context k1 C) d,
                 dec_proc t (lam_c x =: c) d ->   (*!*)
                 dec_proc (Lam x t) c d
  | d_LamECa : forall x t (c : context k1 ECa) d,
                 decctx_proc (vECaLam x t) c d -> (*!*)
                 dec_proc (Lam x t) c d

  | d_AppC   : forall t1 t2 (c : context k1 C) d,
                 dec_proc t1 (ap_r t2 =: c) d ->
                 dec_proc (App t1 t2) c d
  | d_AppECa : forall t1 t2 (c : context k1 ECa) d,
                 dec_proc t1 (ap_r t2 =: c) d ->
                 dec_proc (App t1 t2) c d


  with decctx_proc {k1} : forall {k2}, value k2 -> 
                              context k1 k2 -> decomp k1 -> Prop :=

  | dc_end        : forall (v : value k1),
                      ~ dead_ckind k1 ->
                      decctx_proc v [.] (d_val v)

  | dc_ap_rLamC   : forall x t0 t (c : context k1 C),
                      decctx_proc (vECaLam x t0) (ap_r t =: c) (d_red (rCApp x t0 t) c)
  | dc_ap_rLamECa : forall x t0 t (c : context k1 ECa),
                      decctx_proc (vECaLam x t0) (ap_r t =: c) (d_red (rECaApp x t0 t) c)

  | dc_ap_rVarC   : forall x t (c : context k1 C) d,
                      dec_proc t (ap_l (vCaVar x) =: c) d ->
                      decctx_proc (vECaVar x) (ap_r t =: c) d
  | dc_ap_rVarECa : forall x t (c : context k1 ECa) d,
                      dec_proc t (ap_l (vCaVar x) =: c) d ->
                      decctx_proc (vECaVar x) (ap_r t =: c) d

  | dc_ap_rAppC   : forall v1 v2 t (c : context k1 C) d,
                      dec_proc t (ap_l (vCaApp v1 v2) =: c) d ->
                      decctx_proc (vECaApp v1 v2) (ap_r t =: c) d
  | dc_ap_rAppECa : forall v1 v2 t (c : context k1 ECa) d,
                      dec_proc t (ap_l (vCaApp v1 v2) =: c) d ->
                      decctx_proc (vECaApp v1 v2) (ap_r t =: c) d

  | dc_ap_lC      : forall v1 v2 (c : context k1 C) d,
                      decctx_proc (vCApp v1 v2) c d ->
                      decctx_proc v2 (ap_l v1 =: c) d
  | dc_ap_lECa    : forall v1 v2 (c : context k1 ECa) d,
                      decctx_proc (vECaApp v1 v2) c d ->
                      decctx_proc v2 (ap_l v1 =: c) d

  | dc_lam_cC     : forall v x (c : context k1 C) d,
                      decctx_proc (vCLam x v) c d ->
                      decctx_proc v (lam_c x =: c) d.

  Scheme dec_proc_Ind    := Induction for dec_proc    Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc Sort Prop.


  Module RS := Lam_NO_RefSem.


  Hint Constructors RS.dec_proc RS.decctx_proc dec_proc decctx_proc.
  Hint Transparent Lam_NO_Strategy.dec_term Lam_NO_Strategy.dec_context.

  Theorem dec_proc_eqv_RS :                       forall {k1 k2} (c : context k1 k2) t d,
      dec_proc t c d <-> RS.dec_proc t c d.

  Proof.
    intros k1 k2 c t d; split; intro H.

  (* -> *) { 
    induction H using dec_proc_Ind with
    (P0 := fun _ v c d _ => RS.decctx_proc v c d); eauto;
    match goal with c : RS.context _ ?k |- RS.decctx_proc _ (?ec =: c) _ => 
    solve
    [ eapply (RS.dc_dec ec c); eauto
    | eapply (RS.dc_val ec c); eauto
    | eapply (RS.dc_term ec c); eauto ]
    end.
  }

 (* <- *) {
    induction H using RS.dec_proc_Ind with
    (P0 := fun _ v c d _ => decctx_proc v c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _        |- _ => destruct t, k2; 
                                                  inversion H; subst
    | H : RS.ST.dec_context ?ec ?k ?v = _ |- _ => destruct ec, k2; 
                                                  dependent_destruction2 v; 
                                                  inversion H; subst
    end; eauto.
 }
 Qed.


  Theorem decctx_proc_eqv_RS :                    forall {k1 k2} (c : context k1 k2) v d,
      decctx_proc v c d <-> RS.decctx_proc v c d.

  Proof.
    intros k1 k2 c v d; split; intro H.

  (* -> *) {
    induction H using decctx_proc_Ind with
    (P := fun _ t c d _ => RS.dec_proc t c d); eauto;
    match goal with c : RS.context _ ?k |- RS.decctx_proc _ (?ec =: c) _ => 
    solve
    [ eapply (RS.dc_dec ec c); eauto
    | eapply (RS.dc_val ec c); eauto
    | eapply (RS.dc_term ec c); eauto ]
    end.
  }

  (* <- *) {
    induction H using RS.decctx_proc_Ind with
    (P := fun _ t c d _ => dec_proc t c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _        |- _ => destruct t, k2; 
                                                  inversion H; subst
    | H : RS.ST.dec_context ?ec ?k ?v = _ |- _ => destruct ec, k2; 
                                                  dependent_destruction2 v; 
                                                  inversion H; subst
    end; 
    solve [eauto].
  }
  Qed.

End Lam_NO_HandDecProc.




Module Lam_NO_HandMachine <: ABSTRACT_MACHINE.

  Module R  := Lam_NO_PreRefSem.
  Module RF := RED_LANG_Facts R.


  Definition term := R.term.
  Inductive ckind := E | F | A.


  Definition ckind_to_R k : R.ckind :=
      match k with E => R.C | F => R.ECa | A => R.CBot end.

  Definition ckind_from_R k : ckind :=
      match k with R.C => E | R.ECa => F | R.CBot => A end.


  Definition val k := R.value (ckind_to_R k).
  Definition value := val E.


  Inductive context : ckind -> Set :=
  | ap_r  : R.term  -> forall k, context k -> context F
  | ap_l  : R.valCa -> forall k, context k -> context E
  | lam_c : R.var   ->           context E -> context E
  | hole  : context E.


  Inductive conf :=
  | Ev : R.term -> forall k, context k   -> conf
  | Ap : forall k (c : context k), val k -> conf.
  Definition configuration := conf.


  Definition load (t : term) : configuration := Ev t E hole.


  Definition final (st : configuration) : option value :=
      match st with
      | Ap E hole v => Some v
      | _           => None
      end.


  Definition is_final (st : configuration) := exists v, final st = Some v.


  Definition next_conf0 (st : configuration) : option configuration :=
      match st with
      | Ev (R.Var x) E c     => Some (Ap E c (R.vCVar x))
      | Ev (R.Var x) F c     => Some (Ap F c (R.vECaVar x))

      | Ev (R.Lam x t) E c   => Some (Ev t _ (lam_c x c))     (*!*)
      | Ev (R.Lam x t) F c   => Some (Ap _ c (R.vECaLam x t)) (*!*)

      | Ev (R.App t1 t2) k c => Some (Ev t1 F (ap_r t2 k c))

      | Ap F (ap_r t2 E c) (R.vECaLam x t1) =>
                                Some (Ev (R.subst x t2 t1) E c)
      | Ap F (ap_r t2 F c) (R.vECaLam x t1) =>
                                Some (Ev (R.subst x t2 t1) F c)

      | Ap F (ap_r t k c)  (R.vECaVar x)    =>
                                Some (Ev t E (ap_l (R.vCaVar x) k c))

      | Ap F (ap_r t k c)  (R.vECaApp a v)  =>
                                Some (Ev t E (ap_l (R.vCaApp a v) k c))

      | Ap E (ap_l a E c) v  => Some (Ap E c (R.vCApp   a v))
      | Ap E (ap_l a F c) v  => Some (Ap F c (R.vECaApp a v))

      | Ap E (lam_c x c) v   => Some (Ap E c (R.vCLam x v))

      | _ => None
      end.
  Definition next_conf (_ : entropy) := next_conf0.

  Definition transition st1 st2 := next_conf0 st1 = Some st2.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Fact trans_computable0 :                              forall (st1 st2 : configuration),
       `(rws) st1 → st2 <-> next_conf0 st1 = Some st2.

  Proof. intuition. Qed.


  Fact trans_computable :                                                 forall st1 st2,
       `(rws) st1 → st2 <-> exists e, next_conf e st1 = Some st2.

  Proof.
   intuition.
   - destruct (entropy_exists) as [e _]; exists e; auto.
   - destruct H; eauto.
  Qed.


  Proposition final_correct :                                                  forall st,
       final st <> None -> ~exists st', `(rws) st → st'.

  Proof.
    destruct st as [? | ? c v]; auto.
    destruct c; auto.
    intros _ [st' H].
    inversion H.
  Qed.


  Class SafeRegion (P : configuration -> Prop) :=
  {
      preservation :                                                      forall st1 st2,
          P st1  ->  st1 → st2  ->  P st2;
      progress :                                                              forall st1,
          P st1  ->  is_final st1 \/ exists st2, st1 → st2
  }.




  Program Fixpoint context_to_R {k} (c : context k) : R.context R.C (ckind_to_R k) :=
      match c with
      | ap_r t k' c' => R.ccons (R.ap_r t)  (context_to_R c')
      | ap_l a k' c' => R.ccons (R.ap_l a)  (context_to_R c')
      | lam_c x c'   => R.ccons (R.lam_c x) (context_to_R c')
      | hole         => R.empty
      end.
  Next Obligation. destruct k'; auto. inversion c'. Defined.
  Next Obligation. destruct k'; auto. inversion c'. Defined.


  Program Fixpoint context_from_R
      {k} (c : R.context R.C k) (H : ~R.dead_ckind k) : context (ckind_from_R k) :=

      match c with
      | R.empty => hole
      | @R.ccons _ (R.ap_r t) k' c' => ap_r t (ckind_from_R k') (context_from_R c' _)
      | @R.ccons _ (R.ap_l a) k' c' => ap_l a (ckind_from_R k') (context_from_R c' _)
      | R.ccons    (R.lam_c x)   c' => lam_c x  (context_from_R c' _)
      end.

  Ltac ob_solve1 := solve [eauto using RF.death_propagation2
                          | destruct_all R.ckind; autof ].
  Next Obligation. ob_solve1. Defined.
  Next Obligation. ob_solve1. Defined.
  Next Obligation. ob_solve1. Defined.
  Next Obligation. ob_solve1. Defined.
  Next Obligation. ob_solve1. Defined.
  Next Obligation. ob_solve1. Defined.
  Next Obligation. ob_solve1. Defined.


  Lemma context_from_to_R_eq :                              forall {k} (c : context k) H,
      context_from_R (context_to_R c) H ~= c.

  Proof.
    induction c as [t k c | v k c | x c | ]; intro H;
    [ destruct c
    | destruct c
    | simpl
    | ].

    all: try solve [
         apply JM_eq_from_eq;
         simpl; f_equal;
         apply JMeq_eq; 
         apply IHc ].

    1:   solve [auto].
  Qed.


  Lemma context_to_from_R_eq :                        forall {k} (c : R.context R.C k) H,
      context_to_R (context_from_R c H) ~= c.

  Proof.
    induction c as [ | [x | v | t ] k c]; intro H;
    [
    | destruct k
    | destruct k
    | ].

    1:   solve [auto].

    all: try solve [
      apply JM_eq_from_eq;
      simpl; f_equal;
      apply JMeq_eq; 
      apply IHc].

    all: try solve [autof].

    all:
      let tac := (
          apply JM_eq_from_eq;
          simpl; f_equal;
          apply JMeq_eq;
          apply IHc)
      in

      solve 
      [ dependent destruction c; auto; destruct k2, ec; inversion x0; dep_subst; tac
      | dependent destruction c; auto; destruct k2, ec; autof; tac].
  Qed.




  Module EAM := Lam_NO_EAM.

  Program Definition conf_to_R (st : configuration) : EAM.configuration :=
      match st with
      | Ev t k c => submember_by _ (EAM.RAW.c_eval t (context_to_R c)) _
      | Ap A c v => match (_ : False) with end
      | Ap E c v => submember_by _ (EAM.RAW.c_apply  (context_to_R c) v) _
      | Ap F c v => submember_by _ (EAM.RAW.c_apply  (context_to_R c) v) _
      end.

  Next Obligation. destruct c; auto. Defined.
  Next Obligation. dependent destruction c. Defined.


  Program Definition conf_from_R (st : EAM.configuration) : configuration :=
      let (st, H) := st in
      match st with
      | @EAM.RAW.c_eval t k c  => Ev t (ckind_from_R k) (context_from_R c _)
      | @EAM.RAW.c_apply k c v => Ap   (ckind_from_R k) (context_from_R c _) v
      end.

  Ltac ob_solve2 := solve [destruct_all R.ckind; autof ].
  Next Obligation. ob_solve2. Defined.
  Next Obligation. ob_solve2. Defined.
  Next Obligation. ob_solve2. Defined.


  Theorem conf_from_to_R_eq :                                forall (st : configuration),
      conf_from_R (conf_to_R st) = st.

  Proof.
    intro st.
    destruct st as [t k c | k c v].
    all: set (k0 := k);
         destruct k; try solve [inversion c].
    all: first [apply (f_equal (Ev t k0)) | apply (f_equal2 (Ap k0))].
    all: apply JMeq_eq;
         eauto using (context_from_to_R_eq c).
  Qed.


  Theorem conf_to_from_R_eq :                            forall (st : EAM.configuration),
      conf_to_R (conf_from_R st) = st.

  Proof.
    intro st.
    destruct st as [[t k c | k c v] W].
    all: apply subset_elem_eq;
         set (k0 := k);
         destruct k; try solve [inversion W].
    all: first [ apply (f_equal  (@EAM.RAW.c_eval t k0)) 
               | apply (f_equal2 (@EAM.RAW.c_apply k0))].
    all: apply JMeq_eq;
         eauto using (context_to_from_R_eq c).
  Qed.


  Theorem next0_imp_EAM :                                                      forall st,
      option_map conf_to_R (next_conf0 st) = EAM.next_conf0 (conf_to_R st).

  Proof.
    intro st.
    destruct st as [t k c | k c v].
    - destruct t, c; simpl; 
      solve [auto].
    - destruct c as [ ? ? c | ? ? c | ? ? | ]; compute in v; dependent destruction v;
      try destruct c;
      solve [simpl; autof].
  Qed.


  Corollary next0_fol_EAM :                                                    forall st,
      option_map conf_from_R (EAM.next_conf0 st) = next_conf0 (conf_from_R st).

  Proof.
    intro st.
    rewrite <- (conf_to_from_R_eq st) at 1.
    rewrite <- (next0_imp_EAM (conf_from_R st)).
    destruct (next_conf0 (conf_from_R st)); simpl.
    1  : rewrite conf_from_to_R_eq.
    all: solve [auto].
  Qed.

End Lam_NO_HandMachine.
