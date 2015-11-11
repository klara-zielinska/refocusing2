Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import refocusing_semantics_derivation.
Require Import refocusing_machine.
Require Import refocusing_machine_correct.
Require Import reduction_semantics_facts.
Require Import lam_ses_no.




Module Lam_SES_NO_HandSem <: RED_SEM Lam_SES_NO_Ref.R.

  Module RF := RED_LANG_Facts Lam_SES_NO_Ref.R.
  Import Lam_SES_NO_PreLang Lam_SES_NO_Ref.R.
  Import RF.


  Inductive __dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=

  | d_Var    : forall n {k1 k2} (c : context k1 k2) d, CECaD k2 ->
                 decctx (vVar n k2) c d ->
                 __dec (Var n) c d

  | d_LamC   : forall t {k1} (c : context k1 C) d,
                 __dec t (lam_c =: c) d -> (*!*)
                 __dec (Lam t) c d
  | d_LamECa : forall t {k1} (c : context k1 ECa) d,
                 decctx (vECaLam t) c d -> (*!*)
                 __dec (Lam t) c d
  | d_LamD  : forall t {k1} (c : context k1 D) d,
                 decctx (vDLam t) c d -> (*!*)
                 __dec (Lam t) c d

  | d_App    : forall t1 t2 {k1 k2} (c : context k1 k2) d, CECa k2 ->
                 __dec t1 (ap_r t2 =: c) d ->
                 __dec (App t1 t2) c d

  | d_AppD   : forall t1 t2 {k1} (c : context k1 D) d,
                 decctx (vDApp t1 t2) c d ->
                 __dec (App t1 t2) c d

  | d_Sub    : forall t1 n t2 {k1 k2} (c : context k1 k2) d, CECaD k2 ->
                 __dec t1 (stag_c (n, st_sub t2) =: c) d ->
                 __dec (Sub t1 n t2) c d

  | d_Shift  : forall t1 n m {k1 k2} (c : context k1 k2) d, CECaD k2 ->
                 __dec t1 (stag_c (n, st_shift m) =: c) d ->
                 __dec (Shift t1 n m) c d


  with decctx : forall {k2}, value k2 -> 
                forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_end        : forall {k} (v : value k),
                      ~ dead_ckind k ->
                      decctx v [.] (d_val v)

  | dc_ap_rLamC   : forall t0 t {k1} (c : context k1 C),
                      decctx (vECaLam t0) (ap_r t =: c) (d_red (rCApp t0 t) c)
  | dc_ap_rLamECa : forall t0 t {k1} (c : context k1 ECa),
                      decctx (vECaLam t0) (ap_r t =: c) (d_red (rECaApp t0 t) c)

  | dc_ap_rVarC   : forall n t {k1} (c : context k1 C) d,
                      __dec t (ap_l (vCaVar n) =: c) d ->
                      decctx (vECaVar n) (ap_r t =: c) d
  | dc_ap_rVarECa : forall n t {k1} (c : context k1 ECa) d,
                      __dec t (ap_l (vCaVar n) =: c) d ->
                      decctx (vECaVar n) (ap_r t =: c) d

  | dc_ap_rAppC   : forall v1 v2 t {k1} (c : context k1 C) d,
                      __dec t (ap_l (vCaApp v1 v2) =: c) d ->
                      decctx (vECaApp v1 v2) (ap_r t =: c) d
  | dc_ap_rAppECa : forall v1 v2 t {k1} (c : context k1 ECa) d,
                      __dec t (ap_l (vCaApp v1 v2) =: c) d ->
                      decctx (vECaApp v1 v2) (ap_r t =: c) d

  | dc_ap_lC      : forall v1 v2 {k1} (c : context k1 C) d,
                      decctx (vCApp v1 v2) c d ->
                      decctx v2 (ap_l v1 =: c) d
  | dc_ap_lECa    : forall v1 v2 {k1} (c : context k1 ECa) d,
                      decctx (vECaApp v1 v2) c d ->
                      decctx v2 (ap_l v1 =: c) d

  | dc_lam_cC     : forall v {k1} (c : context k1 C) d,
                      decctx (vCLam v) c d ->
                      decctx v (lam_c =: c) d

  | dc_sub_cLamC   : forall t d {k1} (c : context k1 C),
                       decctx (vDLam t) (stag_c d =: c) (d_red (rSubLam C I t d) c)
  | dc_sub_cLamECa : forall t d {k1} (c : context k1 ECa), 
                       decctx (vDLam t) (stag_c d =: c) (d_red (rSubLam ECa I t d) c)
  | dc_sub_cLamD   : forall t d {k1} (c : context k1 D), 
                       decctx (vDLam t) (stag_c d =: c) (d_red (rSubLam D I t d) c)

  | dc_sub_cVarC   : forall n d {k1} (c : context k1 C), 
                       decctx (vDVar n) (stag_c d =: c) (d_red (rSubVar C I n d) c)
  | dc_sub_cVarECa : forall n d {k1} (c : context k1 ECa), 
                       decctx (vDVar n) (stag_c d =: c) (d_red (rSubVar ECa I n d) c)
  | dc_sub_cVarD   : forall n d {k1} (c : context k1 D), 
                       decctx (vDVar n) (stag_c d =: c) (d_red (rSubVar D I n d) c)

  | dc_sub_cAppC   : forall t1 t2 d {k1} (c : context k1 C), 
                       decctx (vDApp t1 t2) (stag_c d =: c) 
                                  (d_red (rSubApp C I t1 t2 d) c)
  | dc_sub_cAppECa : forall t1 t2 d {k1} (c : context k1 ECa), 
                       decctx (vDApp t1 t2) (stag_c d =: c) 
                                  (d_red (rSubApp ECa I t1 t2 d) c)
  | dc_sub_cAppD   : forall t1 t2 d {k1} (c : context k1 D), 
                       decctx (vDApp t1 t2) (stag_c d =: c) 
                                  (d_red (rSubApp D I t1 t2 d) c).

  Definition dec := __dec. Arguments dec t {k1 k2} c d.

  Scheme dec_Ind    := Induction for __dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  (* Non-signature entries (helpers): *)

  Lemma dead_dec_dead : 
      forall {k1} (c : context k1 CBot) v d, ~ __dec v c d.

  Proof with autof.
    intros; intro H.
    dependent destruction H...
  Qed.


  Lemma dead_decctx_dead : 
      forall {k1} (c : context k1 CBot) v d, ~ decctx v c d.

  Proof with autof.
    intros; intro H.
    dependent destruction H...
  Qed.


  Ltac inj_vr := 
      match goal with
      | [Hv : value_to_term _ = value_to_term _ |- _] => 
            apply value_to_term_injective in Hv
      | [Hv : valCa_to_term _ = valCa_to_term _ |- _] => 
            apply valCa_to_term_injective in Hv
      | [Hr : redex_to_term _ = redex_to_term _ |- _] => 
            apply redex_to_term_injective in Hr
      | [ |- _] => idtac
      end.


  Lemma dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
                           dec (v : term) c d <-> decctx v c d.

  Proof with auto.
    induction v using Lam_SES_NO_Ref_minus.SX.val_Ind with
    (P := fun k2 (v : value k2) => forall (k1 : ckind) (c : context k1 k2)
              (d : decomp k1), dec (v : term) c d <-> decctx v c d)
    (P0:= fun v0 : valCa => forall (k1 k2 : ckind) (c : context k1 k2) (v : value k2)
              (d : decomp k1), (valCa_to_term v0 : term) = (v : term) -> 
              (dec (v : term) c d <-> decctx v c d));

    intros;
    try match goal with [ H: (valCa_to_term ?v0) = (value_to_term ?v1) |- _ ] => 
        match type of v0 with valCa => 
            destruct v1; autof; 
            inversion H; repeat inj_vr; subst; 
            clear H
        end
    end;

    split; intro H1;

    dependent destruction H1;
    try solve
    (* Cases of: dec v c d -> decctx v c d. *)
    [ rewrite IHv in H1;
      dependent destruction H1;
      auto
    | match goal with v : valCa |- _ =>
      destruct valCa_is_valECa with v as (v', H2);
      destruct v; dependent destruction v'; autof;
      inversion H2; repeat inj_vr; subst;
      rewrite H2 in H1;
      rewrite IHv in H1; auto;
      dependent destruction H1;
      match goal with v0 : val _ |- _ => match goal with H : __dec (_ v0) _ _ |- _ =>
      rewrite IHv0 in H;
      dependent_destruction2 H;
      auto
      end end end 
    | match goal with H : __dec _ _ _ |- _ =>
      contradiction (dead_dec_dead _ _ _ H)
      end
    | match goal with H : Var _ = _ |- _ => 
      dependent destruction v; 
      inversion H; subst; 
      simpl in *; tauto 
      end

    (* Cases of: dec v c d <- decctx v c d. *)
    | first [apply d_AppD | constructor]; (* imaginary fold *)
      try (rewrite IHv; constructor); 
      constructor; 
      auto
    | match goal with v : valCa |- _ =>
      constructor; simpl; auto; (* imaginary fold *) fold valCa_to_term;
      destruct valCa_is_valECa with v as (v', H2);
      destruct v; dependent destruction v'; autof;
      inversion H2; repeat inj_vr; subst;
      rewrite H2;
      rewrite IHv; auto; constructor;
      rewrite IHv0; constructor;
      constructor;
      auto
      end

    (* Cases of both implications. *)
    | autof ].
  Qed.



  (* Signature entries: *)

  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> c[t] = d.
  Proof with auto.
    induction 1 using dec_Ind with
    (P  := fun t _ _ c d (_ : dec t c d)    => c[t] = d)
    (P0 := fun _ v _ c d (_ : decctx v c d) => c[v] = d)...
    
    - destruct k2...
  Qed.


  Lemma dec_plug :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c ~+ c0) d.
  Proof.
    intros k1 k2.
    induction c.
    - auto.
    - intros k3 c0 t0 d H H0.
      destruct ec0;
          destruct_all sub_tag; destruct_all substitut;
          assert (hh := IHc _ _ _ _ (death_propagation2 _ _ H) H0);
          dependent destruction hh; subst;
          try destruct k2; autof;
      solve
      [ autof
      | destruct valCa_is_valECa with v as (v', H2);
        destruct v; dependent destruction v'; 
        solve
        [ autof
        | inversion H2; repeat inj_vr; subst;
          rewrite H2 in hh;
          rewrite dec_val_self in hh;
          dependent destruction hh;
          auto 
      ] ].
  Qed.


  Lemma dec_plug_rev :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec t (c ~+ c0) d -> dec c[t] c0 d.
  Proof.
    induction c.
    - auto.
    - intros k3 c0 t d H H0.
      simpl.
      apply IHc; eauto using death_propagation2.
      destruct ec0, k2;
      destruct_all sub_tag; destruct_all substitut;
      try solve 
      [ autof 
      | constructor; simpl; auto
      | match goal with v : valCa |- _ =>
        destruct (valCa_is_valECa v) as (v', H1);
        destruct v; dependent destruction v'; 
        inversion H1; repeat inj_vr; subst;
        constructor; try solve [simpl; auto];
        rewrite H1;
        apply dec_val_self;
        constructor;
        assumption
        end ].
  Qed.


  Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec (redex_to_term r) c (d_red r c).
  Proof with auto.
    destruct r as [t1 t2 | t1 t2 | k H n d | k H t d | k H t1 t2 d];
    destruct_all sub_tag; destruct_all substitut;
    try solve
    [ intros;
      constructor; try solve [simpl; auto];
      first 
      [ destruct k; destruct H; first [apply d_AppD | constructor]; simpl; autof
      | rewrite (dec_val_self (vECaLam t1)) ];
      constructor ].
  Qed.


  Lemma dec_value_self : forall {k} (v : value k), 
                             ~ dead_ckind k -> dec v [.] (d_val v).
  Proof with auto.
    intros k v H.
    apply dec_val_self.
    constructor...
  Qed.


  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall {t k} {d : decomp k}, dec t [.] d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
                contract r = Some t -> decempty c[t] d -> iter d v ->
                iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind}, 
                  decempty t d -> iter d v -> eval t v.

End Lam_SES_NO_HandSem.




Module Lam_SES_NO_RefSem_Check.

  Import Lam_SES_NO_PreLang Lam_SES_NO_Ref.R Lam_SES_NO_Ref.ST.

  Module HS := Lam_SES_NO_HandSem.
  Module RS := Lam_SES_NO_RefSem.


  Lemma HS_dec_imp_RS_dec : 
      forall t {k1 k2} (c : context k1 k2) d, HS.dec t c d -> RS.dec t c d.

  Proof.
    induction 1 using HS.dec_Ind with
    (P := fun t _ _ c d (_ : HS.dec t c d)    =>  RS.dec t c d)
    (P0:= fun _ v _ c d (_ : HS.decctx v c d) =>  RS.decctx v c d);
    try destruct k2; autof;
    try solve
    [ econstructor; simpl; eauto (* - sementicaly this is enough, but Ltac is 
                                      too weak, so we need to be more explicite *)
    | eapply @RS.d_term; simpl; eauto 
    | eapply @RS.dc_dec  with (ec:=ap_r _)   (k2:= C);   simpl; auto
    | eapply @RS.dc_term with (ec:=ap_r _)   (k2:= C);   simpl; eauto 
    | eapply @RS.dc_dec  with (ec:=ap_r _)   (k2:= ECa); simpl; auto
    | eapply @RS.dc_term with (ec:=ap_r _)   (k2:= ECa); simpl; eauto
    | eapply @RS.dc_val  with (ec:=ap_l _)   (k2:= C);   simpl; auto
    | eapply @RS.dc_val  with (ec:=ap_l _)   (k2:= ECa); simpl; auto
    | eapply @RS.dc_val  with (ec:=lam_c)    (k2:= C);   simpl; auto
    | eapply @RS.dc_dec  with (ec:=stag_c _) (k2:= C);   simpl; auto
    | eapply @RS.dc_dec  with (ec:=stag_c _) (k2:= ECa); simpl; auto
    | eapply @RS.dc_dec  with (ec:=stag_c _) (k2:= D);   simpl; auto ].
  Qed.
 

  Lemma RS_dec_imp_HS_dec : 
      forall t {k1 k2} (c : context k1 k2) d, RS.dec t c d -> HS.dec t c d.

  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun t _ _ c d (_ : RS.dec t c d)    => HS.dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => HS.decctx v c d);
    try solve 
    [ match goal with H : dec_term _ _ = _ |- _ =>
      destruct t, k2; 
      inversion H; subst; 
      first [apply HS.d_AppD | constructor]; simpl; auto
      end
    | match goal with H : dec_context _ _ _ = _ |- _ =>
      destruct ec0, k2; dependent destruction v; 
      inversion H; subst; 
      constructor; auto
      end 
    | constructor; auto ].
  Qed.


  Lemma dec_eqv : 
      forall t {k1 k2} (c : context k1 k2) d, HS.dec t c d <-> RS.dec t c d.

  Proof.
    split;
    solve[ eauto using RS_dec_imp_HS_dec, HS_dec_imp_RS_dec ].
  Qed.


  Lemma decempty_eqv : 
      forall t {k} (d : decomp k), HS.decempty t d <-> RS.RS.decempty t d.

  Proof with auto.
    split; 

    solve
    [ intro H;
      dependent_destruction2 H;
      constructor;
      apply dec_eqv; auto ].
  Qed.


  Lemma iter_eqv : forall {k} (d : decomp k) v, 
                           HS.iter d v <-> RS.RS.iter d v.
  Proof.
    split;
 
    solve
    [ intro H;
      dependent induction H;
      solve
      [ constructor
      | econstructor; 
        solve 
        [ eauto
        | eapply decempty_eqv; eauto
    ] ] ].
  Qed.


  Theorem eval_eqv : 
      forall t v, HS.eval t v <-> RS.RS.eval t v.

  Proof with auto.
    split;

    solve
    [ intro H;
      dependent destruction H;
      econstructor;
      [ apply decempty_eqv; eauto
      | apply iter_eqv; eauto
    ] ].
  Qed.

End Lam_SES_NO_RefSem_Check.




Module Lam_SES_NO_HandMachine <: ABSTRACT_MACHINE.

  Import Lam_SES_NO_EAM.
  Import Lam_SES_NO_PreLang.

  Definition contextD := (context C C + context C ECa + context C D) %type.
  Definition contextC := (context C C + context C ECa) %type.
  Definition contextA := context C C.

  Notation "[$ t $]"       := (c_eval t  [.])    (t at level 99).
  Notation "[: v :]"       := (c_apply [.] v)    (v at level 99).
  Notation "[$ t , c $]"   := (c_eval t c)       (t, c at level 99).
  Notation "[: c , v :]"   := (c_apply c v)      (c, v at level 99).

  Reserved Notation "c1 → c2" (at level 40).


  Lemma pre_sub_CECaD_is_CECaD : forall k d, CECaD (k+>stag_c d) -> CECaD k.
  Proof. destruct k, d; simpl; auto. Qed.

  Lemma pre_ap_r_CECa_is_CECa : forall k t, CECa (k+>ap_r t) -> CECa k.
  Proof. destruct k; simpl; auto. Qed.

  Definition bs {A} (devil : False) : A := match devil with end.

  Definition rCECaApp t1 t2 k : CECa k -> redex k :=
      match k as k return CECa k -> redex k with
      | C    => fun _ => rCApp t1 t2 
      | ECa  => fun _ => rECaApp t1 t2
      | D    => bs
      | CBot => bs
      end.


  Inductive trans : configuration -> configuration -> Prop :=

  (* refocus *)

  | t_evVar      : forall n {k1 k2} (c : context k1 k2), CECaD k2 ->
                    [$ Var n, c $]     → [: c, vVar n k2 :]

  | t_evLamD     : forall t {k1} (c : context k1 D),
                    [$ Lam t, c $] → [: c, vDLam t :]

  | t_evLamECa : forall t {k1} (c : context k1 ECa),
                    [$ Lam t, c $] → [: c, vECaLam t :]

  | t_evLamC     : forall t {k1} (c : context k1 C),
                    [$ Lam t, c $] → [$ t, lam_c =: c $]

  | t_evAppD   : forall t1 t2 {k1} (c : context k1 D),
                    [$ App t1 t2, c $] → [: c, vDApp t1 t2 :]

  | t_evAppECa   : forall t1 t2 {k1} (c : context k1 ECa),
                    [$ App t1 t2, c $] → [$ t1, ap_r t2 =: c $]
  | t_evAppC     : forall t1 t2 {k1} (c : context k1 C),
                    [$ App t1 t2, c $] → [$ t1, ap_r t2 =: c $]

  | t_evSub      : forall t1 j t2 {k1 k2} (c : context k1 k2), CECaD k2 ->
                    [$ Sub t1 j t2, c $]  → [$ t1, stag_c (j, st_sub t2) =: c $]

  | t_evShift    : forall t1 j g {k1 k2} (c : context k1 k2), CECaD k2 ->
                    [$ Shift t1 j g, c $] → [$ t1, stag_c (j, st_shift g) =: c $]


  (* aux_D *)

  | t_apSubAppD  : forall t1 t2 {k1} (c : context k1 D) d,
                    [: stag_c d =: c, vDApp t1 t2 :] → [$ contract0 (rSubApp D I t1 t2 d), c $]
  | t_apSubAppECa: forall t1 t2 {k1} (c : context k1 ECa) d,
                    [: stag_c d =: c, vDApp t1 t2 :] → [$ contract0 (rSubApp D I t1 t2 d), c $]
  | t_apSubAppC  : forall t1 t2 {k1} (c : context k1 C) d,
                    [: stag_c d =: c, vDApp t1 t2 :] → [$ contract0 (rSubApp D I t1 t2 d), c $]

  | t_apSubLamD  : forall t {k1} (c : context k1 D) d,
                    [: stag_c d =: c, vDLam t :] → [$ contract0 (rSubLam D I t d), c $]
  | t_apSubLamECa: forall t {k1} (c : context k1 ECa) d,
                    [: stag_c d =: c, vDLam t :] → [$ contract0 (rSubLam D I t d), c $]
  | t_apSubLamC  : forall t {k1} (c : context k1 C) d,
                    [: stag_c d =: c, vDLam t :] → [$ contract0 (rSubLam D I t d), c $]

  | t_apSubVarD  : forall i {k1} (c : context k1 D) d,
                    [: stag_c d =: c, vDVar i :] → [$ contract0 (rSubVar D I i d), c $]
  | t_apSubVarECa: forall i {k1} (c : context k1 ECa) d,
                    [: stag_c d =: c, vDVar i :] → [$ contract0 (rSubVar D I i d), c $]
  | t_apSubVarC  : forall i {k1} (c : context k1 C) d,
                    [: stag_c d =: c, vDVar i :] → [$ contract0 (rSubVar D I i d), c $]

  (* aux_C *)

  | t_apAp_rVarECa : forall i {k1} (c : context k1 ECa) t2, 
                       [: ap_r t2 =: c, vECaVar i :] → [$ t2, ap_l (vCaVar i) =: c $]
  | t_apAp_rVarC   : forall i {k1} (c : context k1 C) t2, 
                       [: ap_r t2 =: c, vECaVar i :] → [$ t2, ap_l (vCaVar i) =: c $]

  | t_apAp_rAppECa : forall v1 v2 {k1} (c : context k1 ECa) t2, 
                       [: ap_r t2 =: c, vECaApp v1 v2 :] → [$ t2, ap_l (vCaApp v1 v2) =: c $]
  | t_apAp_rAppC   : forall v1 v2 {k1} (c : context k1 C) t2, 
                       [: ap_r t2 =: c, vECaApp v1 v2 :] → [$ t2, ap_l (vCaApp v1 v2) =: c $]

  | t_apAp_rLamECa : forall t1 {k1} (c : context k1 ECa) t2, 
                       [: ap_r t2 =: c, vECaLam t1 :] → [$ contract0 (rECaApp t1 t2), c $]
  | t_apAp_rLamC   : forall t1 {k1} (c : context k1 C) t2, 
                       [: ap_r t2 =: c, vECaLam t1 :] → [$ contract0 (rECaApp t1 t2), c $]

  (* aux_A *)

  | t_apAp_lECa    : forall (v2 : value C) {k1} (c : context k1 ECa) v1,
                       [: ap_l v1 =: c, v2 :] → [: c, vECaApp v1 v2 :]
  | t_apAp_lC      : forall (v2 : value C) {k1} (c : context k1 C) v1,
                       [: ap_l v1 =: c, v2 :] → [: c, vCApp v1 v2 :]

  | t_apLam_cC     : forall (v : value C) {k1} (c : context k1 C), 
                       [: lam_c =: c, v :] → [: c, vCLam v :]

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.


  Lemma final_correct : forall v st, ~ c_final v → st.
  Proof. inversion 1. Qed.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall {c0 c1 : configuration}, 
                   c0 → c1 -> trans_close c0 c1
  | multi_step : forall {c0 c1 c2 : configuration}, 
                   c0 → c1 -> trans_close c1 c2 -> trans_close c0 c2
  where "c1 →+ c2" := (trans_close c1 c2).


  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall t (v : val init_ckind), trans_close (c_init t) (c_final v) -> eval t v.


  Definition term          := term.
  Definition value         := value init_ckind.
  Definition configuration := configuration.
  Definition c_init        := c_init.
  Definition c_final       := c_final.

End Lam_SES_NO_HandMachine.




Module Lam_SES_NO_Machine_Check.

  Module EAM := Lam_SES_NO_EAM.
  Module HM  := Lam_SES_NO_HandMachine.
  Import EAM HM.
  Import Lam_SES_NO_PreLang Lam_SES_NO_Strategy.


  Notation "c1 >> c2"  := (Lam_SES_NO_EAM.transition c1 c2)  
               (at level 40, no associativity).
  Notation "c1 >>+ c2" := (Lam_SES_NO_EAM.trans_close c1 c2) 
               (at level 40, no associativity).



  Lemma trans_EAM2HM : forall c0 c1,  c0 >> c1  ->  c0 → c1.
  Proof.
    inversion 1; subst;
    capture_all ckind term context value redex @contract;
    capture_all dec_term dec_context @in_red @in_val @in_term;
    match goal with
    | H : dec_term ?t ?k2 = _ |- _        => destruct t, k2; 
                                             inversion H; subst
    | H : dec_context ?ec ?k2 ?v = _ |- _ => destruct ec, k2; dependent_destruction2 v; 
                                             inversion H; subst
    end;
    try match goal with
    | H : contract _ = Some _ |- _ => inversion H
    end;

    solve [ constructor; simpl; auto ].
  Qed.


  Lemma trans_HM2EAM : forall c0 c1,  c0 → c1  ->  c0 >> c1.
  Proof with auto.
    inversion 1; subst;
    try match goal with
    | H : CECaD ?k |- _ => destruct k; inversion H
    | H : CECaD ?k |- _ => destruct k; inversion H
    end;
    solve [ econstructor; simpl; auto ].
  Qed.


  Lemma trans_eqv : forall c0 c1,  c0 → c1  <->  c0 >> c1.
  Proof.
    split; 
    solve [ auto using trans_HM2EAM, trans_EAM2HM ].
  Qed.


  Lemma tramsCl_eqv : forall c0 c1,  c0 →+ c1  <->  c0 >>+ c1.
  Proof.
    split;

    solve
    [ intro H;
      induction H;
      [ constructor 1;  apply trans_eqv; auto
      | econstructor 2; solve [eauto | apply trans_eqv; eauto]
    ] ].
  Qed.


  Theorem eval_eqv : forall t v, HM.eval t v <-> EAM.eval t v.
  Proof.
    split;
    
    solve
    [ intro H;
      destruct H;
      constructor;
      apply tramsCl_eqv; auto ].
  Qed.


End Lam_SES_NO_Machine_Check.