Require Import Program
               Entropy
               Util
               rewriting_system
               lam_no
               abstract_machine
               reduction_semantics
               reduction_languages_facts.




Module Lam_NO_HandDecProc.

  Module RF := RED_LANG_Facts Lam_NO_RefLang.
  Import Lam_NO_RefLang RF.



  Inductive dec_proc {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | d_VarC   : forall x (c : context k1 C) d,
                 decctx_proc (vCVar x) c d ->
                 dec_proc (Var x) c d 
  | d_VarECa : forall x (c : context k1 ECa) d,
                 decctx_proc (vECaVar x) c d ->
                 dec_proc (Var x) c d 

  | d_LamC   : forall x t (c : context k1 C) d,
                 dec_proc t (lam_c x =: c) d -> (*!*)
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
    end; eauto.
 }
 Qed.

End Lam_NO_HandDecProc.





Module Lam_NO_HandMachine <: ABSTRACT_MACHINE.

  Import Lam_NO_EAM Lam_NO_RefLang.


  Definition term          := term.
  Definition value         := value init_ckind.
  Definition configuration := configuration.
  Definition load          := load.
  Definition value_to_conf := value_to_conf.
  Definition final         := final.

  Notation "[$ t $]"         := (load t)                                 (t at level 99).
  Notation "[: v :]"         := (value_to_conf v)                        (v at level 99).
  Notation "[$ t , k , c $]" := (@c_eval t k c)                    (t, k, c at level 99).
  Notation "[: c , v :]"     := (c_apply c v)                         (c, v at level 99).
  Notation "[: ( ec , k ) =: c , v :]" := (c_apply (@ccons _ ec k c) v)  
                                                               (ec, k, c, v at level 99).


  Definition next_conf0 (st : configuration) : option configuration :=
      match st with
      | [$ Var x, C,   c $]     => Some [: c, vCVar x :]
      | [$ Var x, ECa, c $]     => Some [: c, vECaVar x :]

      | [$ Lam x t, C,   c $]   => Some [$ t, C, lam_c x=:c $] (*!*)
      | [$ Lam x t, ECa, c $]   => Some [: c, vECaLam x t :]   (*!*)

      | [$ App t1 t2, C,   c $] => Some [$ t1, ECa, ap_r t2=:c $]
      | [$ App t1 t2, ECa, c $] => Some [$ t1, ECa, ap_r t2=:c $]

      | [: (ap_r t2, C)=:c,   vECaLam x t1 :] => 
                                   Some [$ contract0 (rCApp x t1 t2), C, c $]
      | [: (ap_r t2, ECa)=:c, vECaLam x t1 :] => 
                                   Some [$ contract0 (rECaApp x t1 t2), ECa, c $]

      | [: (ap_r t,  C)=:c,   vECaVar x :] => 
                                   Some [$ t, C, ap_l (vCaVar x)=:c $]
      | [: (ap_r t,  ECa)=:c, vECaVar x :] =>
                                   Some [$ t, C, ap_l (vCaVar x)=:c $]

      | [: (ap_r t,  C)=:c,   vECaApp v1 v2 :] =>
                                   Some [$ t, C, ap_l (vCaApp v1 v2)=:c $]
      | [: (ap_r t,  ECa)=:c, vECaApp v1 v2 :] =>
                                   Some [$ t, C, ap_l (vCaApp v1 v2)=:c $]

      | [: (ap_l v1, C)=:c,   v2 :] => Some [: c, vCApp v1 v2 :]
      | [: (ap_l v1, ECa)=:c, v2 :] => Some [: c, vECaApp v1 v2 :]

      | [: (lam_c x, C)=:c, v :]    => Some [: c, vCLam x v :]

      | _ => None
      end.
  Definition next_conf (_ : entropy) := next_conf0.

  Definition transition st1 st2 := next_conf0 st1 = Some st2.

  Instance rws : REWRITING_SYSTEM :=
  { configuration := configuration; transition := transition }.

(* Uncomment if you don't want to use classes :
  Notation "c1 → c2"  := (transition c1 c2)              (no associativity, at level 70).
  Notation "t1 →+ t2" := (clos_trans_1n _ transition t1 t2)
                                                         (no associativity, at level 70).
  Notation "t1 →* t2" := (clos_refl_trans_1n _ transition t1 t2)
                                                         (no associativity, at level 70).
*)

  Fact trans_computable0 :                                       forall (st1 st2 : conf),
       `(rws) st1 → st2 <-> next_conf0 st1 = Some st2.

  Proof. intuition. Qed.


  Fact trans_computable :                                                 forall st1 st2,
       `(rws) st1 → st2 <-> exists e, next_conf e st1 = Some st2.

  Proof. 
   intuition. 
   - destruct (draw_fin_correct 1 Fin.F1) as [e _]; exists e; auto.
   - destruct H; eauto.
  Qed.




  Theorem next_conf0_eq_EAM :                                                  forall st,
      next_conf0 st = Lam_NO_EAM.next_conf0 st.

  Proof.
    destruct st as [t k ? | k c v].
    - destruct t, k; eauto.
    - destruct c as [| ec k c]; eauto.
      destruct ec, k; dependent destruction v; eauto.
  Qed.


  Corollary next_conf_eq_EAM :                                               forall e st,
      next_conf e st = Lam_NO_EAM.next_conf e st.

  Proof. eauto using next_conf0_eq_EAM. Qed.


  Corollary transition_eqv_EAM :                                          forall st1 st2,
      `(Lam_NO_EAM.rws) st1 → st2  <->  `(rws) st1 → st2.

  Proof.
    intros.
    rewrite trans_computable, Lam_NO_EAM.trans_computable.
    unfold Lam_NO_EAM.next_conf, next_conf.
    rewrite next_conf0_eq_EAM.
    intuition.
  Qed.


  Proposition final_correct :                                                  forall st,
       final st <> None -> ~exists st', `(rws) st → st'.

  Proof.
    destruct st as [? | ? c v]; auto.
    destruct c; auto.
    intros _ [st' H].
    inversion H.
  Qed.


  Fact finals_are_vals :                                                     forall st v,
       final st = Some v <-> st = v. 

  Proof. exact Lam_NO_EAM.finals_are_vals. Qed.

End Lam_NO_HandMachine.
