Require Import Util.
Require Import Program.
Require Import miniml.
Require Import abstract_machine.
Require Import reduction_semantics.
Require Import reduction_semantics_facts.



Module MiniML_HandSem <: RED_SEM MiniML_Ref.R.

  Module RF := RED_LANG_Facts MiniML_Ref.R.
  Import MiniML_SX MiniML_Ref.
  Import RF.

(*
  Lemma decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

  Proof with simpl; f_equal; eauto.
    intros t () _.

    induction t.

    - left.
      exists vZ...

    - destruct IHt as [(v, ?) | ((), (r, (c, ?)))].
      + left.
        exists (vS v)...
      + right.
        exists () r (c ~+ s_c =: [.](())).
        rewrite plug_compose...

    - right; exists ().
      destruct IHt1 as [(v1, ?) | ((), (r1, (c1, ?)))].
      + destruct IHt2 as [(v2, ?) | ((), (r2, (c2, ?)))].
        * exists (rApp v1 v2) [.](())...
        * exists r2 (c2 ~+ ap_l v1 =: [.](())).
          rewrite plug_compose...
      + exists r1 (c1 ~+ ap_r t2 =: [.](())).
        rewrite plug_compose...

    - left.
      eexists (vVar _)...

    - left.
      eexists (vLam _ _)...

    - right.
      destruct IHt1 as [(v1, ?) | ((), (r, (c, ?)))].
      + eexists (), (rCase v1 _ _ _), [.]...
      + eexists (), r, (c ~+  case_c _ _ _ =: [.]).
        rewrite plug_compose...

    - right.
      destruct IHt1 as [(v1, ?) | ((), (r, (c, ?)))].
      + eexists (), (rLet _ _ _), [.]...
      + eexists (), r, (c ~+ let_c _ _ =: [.]).
        rewrite plug_compose...

    - right.
      eexists (), (rFix _ _), [.]...

    - destruct IHt1 as [(v1, ?) | ((), (r1, (c1, ?)))].
      + destruct IHt2 as [(v2, ?) | ((), (r2, (c2, ?)))].
        * left.
          exists (vPair v1 v2)...
        * right.
          eexists (), r2, (c2 ~+ pair_l v1 =: [.]).
          rewrite plug_compose...
      + right.
        eexists (), r1, (c1 ~+ pair_r t2 =: [.]).
        rewrite plug_compose...

    - right.
      destruct IHt as [(v, ?) | ((), (r, (c, ?)))].
      + eexists (), (rFst v), [.]... 
      + eexists (), r, (c ~+ fst_c =: [.]).
        rewrite plug_compose...

    - right.
      destruct IHt as [(v, ?) | ((), (r, (c, ?)))].
      + eexists (), (rSnd v), [.]... 
      + eexists (), r, (c ~+ snd_c =: [.]).
        rewrite plug_compose...
  Qed.*)

  Notation value' := (value ()).
  Notation context' := (context () ()).
  Notation decomp' := (decomp ()).


  Inductive __dec : term -> context' -> decomp' -> Prop :=

  | d_z   : forall c d, __decctx vZ c d             -> __dec Z c d

  | d_s   : forall t c d, __dec t (s_c =: c) d      -> __dec (S t) c d

  | d_case: forall t ez x es c d, 
              __dec t (case_c ez x es =: c) d       -> __dec (Case t ez x es) c d

  | d_var : forall x c d, __decctx (vVar x) c d     -> __dec (Var x) c d

  | d_lam : forall x t c d, __decctx (vLam x t) c d -> __dec (Lam x t) c d

  | d_app : forall t1 t2 c d, 
              __dec t1 (ap_r t2 =: c) d             -> __dec (App t1 t2) c d

  | d_let : forall x t e c d, 
              __dec t (let_c x e =: c) d            -> __dec (Letv x t e) c d

  | d_fix : forall x t c, 
              __dec (Fix x t) c (d_red (rFix x t) c)

  | d_pair: forall t1 t2 c d, 
              __dec t1 (pair_r t2 =: c) d           -> __dec (Pair t1 t2) c d

  | d_fst : forall t c d, __dec t (fst_c =: c) d    -> __dec (Fst t) c d

  | d_snd : forall t c d, __dec t (snd_c =: c) d    -> __dec (Snd t) c d


  with __decctx : value' -> context' -> decomp' -> Prop :=

  | dc_em : forall v,
              __decctx v [.] (d_val v)

  | dc_s  : forall v c d, __decctx (vS v) c d       -> __decctx v (s_c =: c) d

  | dc_cs : forall v x ez es (c : context'),
              __decctx v (case_c ez x es =: c) (d_red (rCase v ez x es) c)

  | dc_apr: forall v t (c : context') d, 
              __dec t (ap_l v =: c) d               -> __decctx v (ap_r t =: c) d

  | dc_apl: forall v v0 (c : context'),
              __decctx v (ap_l v0 =: c) (d_red (rApp v0 v) c)

  | dc_let: forall v x e (c : context'),
              __decctx v (let_c x e =: c) (d_red (rLet x v e) c)

  | dc_p_r: forall t v (c : context') d, 
              __dec t (pair_l v =: c) d             -> __decctx v (pair_r t =: c) d

  | dc_p_l: forall v v0 c d, 
              __decctx (vPair v0 v) c d             -> __decctx v (pair_l v0 =: c) d

  | dc_fst: forall v (c : context'), 
              __decctx v (fst_c =: c) (d_red (rFst v) c)

  | dc_snd: forall v (c : context'),
              __decctx v (snd_c =: c) (d_red (rSnd v) c).


  Definition dec : 
      term -> forall {k1 k2 : ckind}, context k1 k2 -> decomp k1 -> Prop := 
      fun t => ##(__dec t).

  Definition decctx : 
      forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
      #(fun v => #(__decctx v)).

  Scheme dec_Ind    := Induction for __dec    Sort Prop
    with decctx_Ind := Induction for __decctx Sort Prop.


  Lemma dec_val_self : forall (v : value') c d, __dec v c d <-> __decctx v c d.
  Proof.
    induction v;
        intros c d; split; intro H;
        inversion H; dep_subst; 

    solve
    [ auto

    | constructor; auto

    | match goal with H : _ |- _ => 
      apply IHv in H;
      inversion H1; dep_subst;
      solve [ auto ]
      end

    | match goal with H : _ |- _ => 
      apply IHv1 in H;
      inversion H; dep_subst;
      match goal with H : _ |- _ => 
      apply IHv2 in H;
      inversion H; dep_subst;
      solve [ auto ]
      end end

    | constructor; fold (@value_to_term ()); 
      apply IHv; 
      constructor;
      auto

    | constructor; fold (@value_to_term ());
      apply IHv1; constructor;
      apply IHv2; constructor;
      auto ].
  Qed.



  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> c[t] = d.
  Proof with auto.
    destruct k1, k2.
    induction 1 using dec_Ind with
    (P  := fun t c d (_ : __dec t c d)  => c[t] = d)
    (P0 := fun v c d (_ : decctx v c d) => c[v] = d)...
  Qed.


  Lemma dec_plug :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c ~+ c0) d.
  Proof.
    induction c.
    - auto.
    - intros k3 c0 t0 d H H0.
      destruct ec0;
          assert (hh := IHc _ _ _ _ (death_propagation2 _ _ H) H0);
          destruct k1, k2, k3; simpl in hh;
          dependent destruction hh; subst;
      solve
      [ auto
      | apply dec_val_self in hh;
        inversion hh; dep_subst;
        auto ].
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
      destruct ec0, k1, k2, k3;
      solve 
      [ constructor; 
        auto
      | constructor;
        apply dec_val_self;
        constructor;
        assumption ].
  Qed.


  Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec (redex_to_term r) c (d_red r c).
  Proof.
    destruct k2, k1.
    destruct r as [v1 v2 | x v t | x t | v | v | v t1 x t2];
        intro c;
    solve 
    [ constructor;
      repeat (apply dec_val_self; constructor); 
      auto ].
  Qed.


  Lemma dec_value_self : forall {k} (v : value k), 
                             ~ dead_ckind k -> dec v [.] (d_val v).
  Proof with auto.
    intros k v H.
    destruct k.
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

End MiniML_HandSem.




Module MiniML_REF_SEM_Check.

  Import MiniML_Ref.

  Module HS := MiniML_HandSem.
  Module RS := MiniML_REF_SEM.


  Lemma HS_dec_imp_RS_dec : 
      forall t {k1 k2} (c : context k1 k2) d, HS.dec t c d -> RS.dec t c d.

  Proof.
    intros t () () c d H.
    induction H using HS.dec_Ind with
    (P := fun t c d (_ : HS.__dec t c d)  =>  RS.dec t c d)
    (P0:= fun v c d (_ : HS.decctx v c d) =>  RS.decctx v c d);
    
    solve 
    [ econstructor 1; simpl; eauto 
    | econstructor 2; simpl; eauto 
    | econstructor 3; simpl; eauto
    | econstructor 4; simpl; eauto ].
  Qed.


  Ltac subst' := repeat
      match goal with _ : ?x = ?y |- _ => try subst x; subst y end.

  Lemma RS_dec_imp_HS_dec : 
      forall t {k1 k2} (c : context k1 k2) d, RS.dec t c d -> HS.dec t c d.

  Proof.
    intros t () () c d H.
    induction H using RS.dec_Ind with
    (P := fun t _ _ c d (_ : RS.dec t c d)    => HS.dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => HS.decctx v c d);
        first [destruct k1, k2 | destruct k];
    try solve
    [ constructor
    | match goal with 
      | H : dec_term _ _ = _ |- _ =>
            destruct t;
            inversion H; subst; 
            constructor; auto
      | H : dec_context ?ec _ ?v = _ |- _ =>
            destruct ec; inversion e; subst'; econstructor; auto
            end ].
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

End MiniML_REF_SEM_Check.




Module MiniML_HandMachine <: ABSTRACT_MACHINE.

  Import MiniML_SX.
  Import MiniML_EAM.

  Notation contract' := (@MiniML_Ref.R.contract ()).

  Notation "[$ t $]"     := (c_init t)    (t at level 99).
  Notation "[: v :]"     := (c_final v)   (v at level 99).
  Notation "[$ t , c $]" := (@c_eval t () () c)  (t, c at level 99).
  Notation "[: c , v :]" := (@c_apply () () c v) (c, v at level 99).


  Reserved Notation "c1 → c2" (at level 40).

  Inductive trans : configuration -> configuration -> Prop :=
  | t_ez   : forall c,           [$ Z, c $]               → [: c, vZ :]
  | t_es   : forall t c,         [$ S t, c $]             → [$ t, s_c =: c $]
  | t_evar : forall x c,         [$ Var x, c $]           → [: c, vVar x :]
  | t_elam : forall x t c,       [$ Lam x t, c $]         → [: c, vLam x t :]
  | t_eapp : forall t1 t2 c,     [$ App t1 t2, c $]       → [$ t1, ap_r t2 =: c $]
  | t_ecas : forall t ez x es c, [$ Case t ez x es, c $]  → [$ t, case_c ez x es =: c $]

  | t_efix : forall x t1 t2 c, contract' (rFix x t1) = Some t2 -> 
                                 [$ Fix x t1, c $]        → [$ t2, c $]

  | t_elet : forall x t1 t2 c,   [$ Letv x t1 t2, c $]    → [$ t1, let_c x t2 =: c $]
  | t_epar : forall t1 t2 c,     [$ Pair t1 t2, c $]      → [$ t1, pair_r t2 =: c $]
  | t_efst : forall t c,         [$ Fst t, c $]           → [$ t, fst_c =: c $]
  | t_esnd : forall t c,         [$ Snd t, c $]           → [$ t, snd_c =: c $]
  | t_as   : forall v c,         [: s_c =: c, v :]        → [: c, vS v :]

  | t_aa_r : forall v t (c : context'),       
                                 [: ap_r t =: c, v :]     → [$ t, ap_l v =: c $]

  | t_aa_l : forall v1 v2 t c, contract' (rApp v1 v2) = Some t -> 
                            [: ap_l v1 =: c, v2 :]        → [$ t, c $]
  | t_acas : forall v ez x es c t, contract' (rCase v ez x es) = Some t ->
                            [: case_c ez x es =: c, v :]  → [$ t, c $]
  | t_alet : forall v x e c t, contract' (rLet x v e) = Some t ->
                            [: let_c x e =: c, v :]       → [$ t, c $]

  | t_ap_r : forall v t (c : context'), 
                                 [: pair_r t =: c, v :]   → [$ t, pair_l v =: c $]

  | t_ap_l : forall v1 v2 c,     [: pair_l v1 =: c, v2 :] → [: c, vPair v1 v2 :]

  | t_afst : forall v c t, contract' (rFst v) = Some t ->
                                 [: fst_c =: c, v :]      → [$ t, c $]
  | t_asnd : forall v c t, contract' (rSnd v) = Some t ->
                                 [: snd_c =: c, v :]      → [$ t, c $]

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.


  Lemma final_correct : forall v st, ~ c_final v → st.

  Proof.
    inversion 1.
  Qed.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall {c0 c1 : configuration}, 
                   c0 → c1 -> trans_close c0 c1
  | multi_step : forall {c0 c1 c2 : configuration}, 
                   c0 → c1 -> trans_close c1 c2 -> trans_close c0 c2
  where "c1 →+ c2 " := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition term          := term.
  Definition value         := value.
  Definition configuration := configuration.
  Definition c_init        := c_init.
  Definition c_final       := c_final.

End MiniML_HandMachine.




Module MiniML_Machine_Check.

  Module EAM := MiniML_EAM.
  Module HM  := MiniML_HandMachine.
  Import MiniML_Ref.ST.
  Import EAM.
  Import HM.


  Notation "a >> b"  := (MiniML_EAM.transition a b)  (at level 40, no associativity).
  Notation "a >>+ b" := (MiniML_EAM.trans_close a b) (at level 40, no associativity).


  Lemma trans_EAM2HM : forall c0 c1,  c0 >> c1  ->  c0 → c1.
  Proof.
    inversion 1;
    match goal with
    | H : dec_term ?t ?k2 = _ |- _        => 
          destruct t, k1, k2; 
          inversion H; subst
    | H : dec_context ?ec ?k2 ?v = _ |- _ => 
          destruct ec, k1, k2; dependent_destruction2 v;
          inversion H; subst
    end;

    solve [ constructor; auto ].
  Qed.


  Lemma trans_HM2EAM : forall c0 c1,  c0 → c1  ->  c0 >> c1.
  Proof with auto.
    inversion 1; subst;
    econstructor; simpl...
  Qed.


  Lemma trans_eqv : forall c0 c1,  c0 → c1  <->  c0 >> c1.
  Proof.
    split; 
    solve [ auto using trans_HM2EAM, trans_EAM2HM ].
  Qed.


  Lemma transCl_eqv : forall c0 c1,  c0 →+ c1  <->  c0 >>+ c1.
  Proof.
    split;
    (
      intro H;
      induction H;
      [ econstructor 1;  apply trans_eqv; auto
      | econstructor 2; solve [eauto | apply trans_eqv; eauto] ]
    ).
  Qed.


  Theorem eval_eqv : forall t v, HM.eval t v <-> EAM.eval t v.
  Proof.
    split;
    
    solve
    [ intro H;
      destruct H;
      constructor;
      apply transCl_eqv; auto ].
  Qed.

End MiniML_Machine_Check.
