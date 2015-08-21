Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import refocusing_lang_facts.
Require Import abstract_machine.




Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) (*<: PRE_ABSTRACT_MACHINE R*).

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.
  Import RS.
  Export DEC.


  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [.] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} {c : context k1 k2} {d v},
              contract r = Some t -> dec t c d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind},
                dec t [.] d -> iter d v -> eval t v.


  Lemma dec_id_l : forall {t k1 k2} {c : context k1 k2} {d}, 
                       RS.RS.dec t c d -> dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t _ _ c d (_ : RS.RS.dec t c d) => dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => decctx v c d);
    solve 
    [ econstructor; eauto
    | eapply d_term; eauto
    | eapply dc_term; eauto ].
  Qed.
  Hint Resolve dec_id_l.


  Lemma dec_id_r : forall {t k1 k2} {c : context k1 k2} {d}, 
                       dec t c d -> RS.RS.dec t c d.
  Proof with eauto.
    induction 1 using dec_Ind with 
    (P := fun t _ _ c d (_ : dec t c d)    => RS.RS.dec t c d)
    (P0:= fun _ v _ c d (_ : decctx v c d) => RS.decctx v c d);
    solve
    [ econstructor; eauto
    | eapply RS.d_term; eauto
    | eapply RS.dc_term; eauto ].
  Qed.
  Hint Resolve dec_id_r.


  Lemma iterRedPam : forall {k} {d : decomp k} {v}, RS.RS.iter d v -> iter d v.
  Proof with eauto.
    induction 1; econstructor...
    dependent destruction H0.
    apply dec_id_l.
    apply RS.RS.dec_plug in H0.
    - rewrite <- compose_empty in H0...
    - eapply proper_death2... exact [.].
  Qed.


  Lemma evalRedPam : forall {t} {v : value init_ckind},  RS.RS.eval t v -> eval t v.
  Proof with eauto.
    intros.
    dependent destruction H;
    econstructor;
    dependent destruction H...
    apply iterRedPam...
  Qed.
  Hint Resolve evalRedPam.


  Lemma iterPamRed : forall {k} {d : decomp k} {v}, iter d v -> RS.RS.iter d v.
  Proof with eauto.
    induction 1.
    - constructor.
    - econstructor...
      constructor.
      apply RS.RS.dec_plug_rev.
      + eapply proper_death2... exact [.].
      + rewrite <- compose_empty...
  Qed.


  Lemma evalPamRed : forall {t} {v : value init_ckind}, eval t v -> RS.RS.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    econstructor.
    - constructor...
    - apply iterPamRed...
  Qed.
  Hint Resolve evalPamRed.


  Theorem evalPam : forall {t} {v : value init_ckind}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    split...
  Qed.


  Module DEC := DEC.

End PreAbstractMachine.




Module StagedAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) (*<: STAGED_ABSTRACT_MACHINE R*).

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.
  Import RS.
  Export DEC.

  Module PAM := PreAbstractMachine R RS.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=
  | d_dec  : forall t {k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> iter (d_red r c) v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> decctx v c v0 ->
               dec t c v0
  | d_many : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> value k1 -> Prop :=
  | dc_end  : forall {k} {v v0 : value k},
               ~ dead_ckind k ->
               iter (d_val v) v0 ->
               decctx v [.] v0
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r v0},
               dec_context ec k2 v = in_red r -> iter (d_red r c) v0 ->
               decctx v (ec=:c) v0
  | dc_val  : forall ec {k2} (v : value (k2+>ec)) {v0 k1} {c : context k1 k2} {v1},
               dec_context ec k2 v = in_val v0 -> decctx v0 c v1 ->
               decctx v (ec=:c) v1
  | dc_term : forall ec {k2} (v : value (k2+>ec)) {t ec0 k1} {c : context k1 k2} {v0},
               dec_context ec k2 v = in_term t ec0 -> dec t (ec0=:c) v0 ->
               decctx v (ec=:c) v0

  with iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), 
               iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {k1} {c : context k1 k2} {t v},
               contract r = Some t -> dec t c v -> 
               iter (d_red r c) v.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop
    with iter_Ind   := Induction for iter Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [.] v -> eval t v.


  Lemma decPamSam : forall {t k1 k2} {c : context k1 k2} {d},
                        PAM.dec t c d -> forall {v}, iter d v -> dec t c v.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P  := fun t _ _ c d (_ : PAM.dec t c d)    => forall v,  iter d v -> dec t c v)
    (P0 := fun _ v _ c d (_ : PAM.decctx v c d) => forall v', iter d v' -> decctx v c v');
    intros; simpl; solve 
    [ econstructor; eauto
    | eapply d_v; eauto
    | eapply d_many; eauto 
    | eapply dc_val; eauto
    | eapply dc_term; eauto ].
  Qed.
  Hint Resolve decPamSam.


  Lemma iterPamSam : forall {k} {d : decomp k} {v}, PAM.iter d v -> iter d v.
  Proof with eauto.
    induction 1; [constructor | econstructor 2]...
  Qed.
  Hint Resolve iterPamSam.


  Lemma evalPamSam : forall {t} {v : value init_ckind}, PAM.eval t v -> eval t v.
  Proof with eauto.
    intros; dependent destruction H; constructor...
  Qed.
  Hint Resolve evalPamSam.


  Module RSP := Red_Sem_Proper R RS.
  Import RSP.


  Lemma decSamPam : forall {t k1 k2} {c : context k1 k2} {v}, dec t c v -> 
                        forall {d}, PAM.dec t c d -> PAM.iter d v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P  := fun t _ _ c v  (_ : dec t c v)     => forall d, PAM.dec t c d -> PAM.iter d v)
    (P0 := fun _ v _ c v' (_ : decctx v c v') => forall d, PAM.decctx v c d -> PAM.iter d v')
    (P1 := fun _ d v      (_ : iter d v)      => PAM.iter d v); 
    try (intros d0 G; dependent destruction G; try inversion_ccons x);
    try solve 
    [ rewrite H in e; inversion e; subst; eauto
    | rewrite H0 in e; inversion e; subst; eauto 
    | eauto
    | constructor ].

    - destruct (dec_total c[t] k1) as [d H0].
        { eapply proper_death2... }
      dependent destruction H0.
      apply RS.RS.dec_plug in H0;
          try solve [eapply proper_death2; eauto; exact [.] ].
      rewrite <- compose_empty in H0.
      econstructor...
  Qed.
  Hint Resolve decSamPam.


  Lemma evalSamPam : forall {t} {v : value init_ckind}, eval t v -> PAM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    destruct (dec_total t init_ckind) as [d H0].
      { dependent destruction H. eapply proper_death2... exact [.].
        dependent destruction H0; try discriminateJM x...
        eapply death_propagation2; eapply dec_term_next_alive... }
    dependent destruction H0;
    econstructor...
  Qed.
  Hint Resolve evalSamPam.


  Theorem evalSam : forall {t} {v : value init_ckind}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros; rewrite PAM.evalPam; split; intros...
  Qed.


  Module DEC := DEC.

End StagedAbstractMachine.



Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) (*<: EVAL_APPLY_MACHINE R*).

  Import R.
  Import RS.
  Export DEC.

  Module SAM := StagedAbstractMachine R RS.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=
  | d_d_r  : forall t {t0 k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> contract r = Some t0 -> dec t0 c v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> decctx v c v0 ->
               dec t c v0
  | d_term : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> value k1 -> Prop :=
  | dc_end : forall {k} (v : value k), 
               ~ dead_ckind k ->
               decctx v [.] v
  | dc_red : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r t v0},
               dec_context ec k2 v = in_red r -> contract r = Some t -> dec t c v0 ->
               decctx v (ec=:c) v0
  | dc_rec : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {v0 v1},
               dec_context ec k2 v = in_val v0 -> decctx v0 c v1 ->
               decctx v (ec=:c) v1
  | dc_trm : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {t ec0 v0},
               dec_context ec k2 v = in_term t ec0 -> dec t (ec0=:c) v0 ->
               decctx v (ec=:c) v0.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [.] v -> eval t v.


  Lemma decSamEam : forall {t k1 k2} {c : context k1 k2} {v}, SAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using SAM.dec_Ind with
    (P := fun t _ _ c v  (_ : SAM.dec t c v)     => dec t c v)
    (P0:= fun _ v _ c v' (_ : SAM.decctx v c v') => decctx v c v')
    (P1:= fun k d v      (_ : SAM.iter d v)      => 
              match d with
              | d_val v'    => ~ dead_ckind k -> decctx v [.] v'
              | d_red _ r c => forall t, contract r = Some t -> dec t c v
              end);
    simpl; intros.

    (* Case 1 *)
    dependent destruction i; subst; econstructor 1...
    (* Case 2 *)
    econstructor 2...
    (* Case 3 *)
    econstructor 3...
    (* Case 4 *)
    assert (IHdec' := IHdec n).
    dependent destruction IHdec'; subst; constructor...
    (* Case 5 *)
    dependent destruction i; econstructor 2...
    (* Case 6 *)
    econstructor 3...
    (* Case 7 *)
    econstructor 4...
    (* Case 8 *)
    constructor...
    (* Case 9 *)
    rewrite e in H0; inversion H0; subst...
  Qed.


  Lemma evalSamEam : forall {t} {v : value init_ckind}, SAM.eval t v -> eval t v.
  Proof.
    intros; dependent destruction H; constructor; apply decSamEam; auto.
  Qed.
  Hint Resolve evalSamEam.


  Lemma decEamSam : forall {t k1 k2} {c : context k1 k2} {v}, dec t c v -> SAM.dec t c v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun t _ _ c v  (_ : dec t c v)     => SAM.dec t c v)
    (P0:= fun _ v _ c v' (_ : decctx v c v') => SAM.decctx v c v'); 
    intros; simpl.

    econstructor 1; try econstructor...
    econstructor 2...
    econstructor 3...
    repeat constructor...
    econstructor 2; try econstructor 2...
    econstructor 3...
    econstructor 4...
  Qed.


  Lemma evalEamSam : forall {t} {v : value init_ckind}, eval t v -> SAM.eval t v.
  Proof.
    intros; dependent destruction H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.


  Theorem evalEam : forall {t} {v : value init_ckind}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros; rewrite SAM.evalSam; split...
  Qed.


  Module DEC := DEC.

End EvalApplyMachine.



Module ProperEAMachine (R : RED_LANG) (RS : RED_REF_SEM R) (*<: PROPER_EA_MACHINE R*).

  Import R.
  Import RS.
  Export DEC.

  Module EAM := EvalApplyMachine R RS.


  Inductive configuration : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> configuration
  | c_apply : forall {k1 k2}, context k1 k2 -> value k2 -> configuration.


  Definition c_init t := c_eval t [.](init_ckind).
  Definition c_final (v : value init_ckind) := c_apply [.] v.


  Reserved Notation " a → b " (at level 40, no associativity).


  Inductive transition : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {r t0},
               dec_term t k2 = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_val  : forall t {k1 k2} (c : context k1 k2) {v},
      	       dec_term t k2 = in_val v ->
               c_eval t c → c_apply c v
  | t_term : forall t {k1 k2} (c : context k1 k2) {t0 ec},
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
  | t_cred : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r t},
               dec_context ec k2 v = in_red r -> contract r = Some t ->
               c_apply (ec=:c) v → c_eval t c
  | t_cval : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {v0},
               dec_context ec k2 v = in_val v0 ->
               c_apply (ec=:c) v → c_apply c v0
  | t_cterm: forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {t ec0},
               dec_context ec k2 v = in_term t ec0 ->
               c_apply (ec=:c) v → c_eval t (ec0=:c)

  where " a → b " := (transition a b).


  Module AM : ABSTRACT_MACHINE
    with Definition term          := term
    with Definition value         := value init_ckind
    with Definition configuration := configuration
    with Definition transition    := transition
    with Definition c_init        := c_init
    with Definition c_final       := c_final.

    Definition term          := term.
    Definition value         := value init_ckind.
    Definition configuration := configuration.
    Definition transition    := transition.
    Definition c_init        := c_init.
    Definition c_final       := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), 
                       transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), 
                       transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).


  Lemma decEamTrans : forall {t k1 k2} (c : context k1 k2) {v}, 
                          EAM.dec t c v -> c_eval t c →+ c_apply [.] v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v)     => 
              c_eval t c  →+ c_apply [.] v)
    (P0:= fun k2 v k1 c v' (_ : EAM.decctx v c v') => 
              c_apply c v →+ c_apply [.] v' \/ k1 = k2 /\ @empty k1 ~= c /\ v ~=v');
    intuition;
    try solve
    [ (try apply or_introl); econstructor 2; eauto; econstructor; eauto 
    | dep_subst; constructor 1; constructor; auto].

    - dep_subst; left; constructor 1; econstructor...
  Qed.
  Hint Resolve decEamTrans.


  Lemma evalEamMachine : forall {t v}, 
                             EAM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    constructor.
    apply decEamTrans...
  Qed.
  Hint Resolve evalEamMachine.


  Lemma transDecEam : forall {t k1 k2} {c : context k1 k2} {v : value k1}, 
                          c_eval t c →+ c_apply [.] v -> EAM.dec t c v.
  Proof with eauto.
    intros t k1 k2 c v; revert t k2 c.
    cut (forall co, co →+ c_apply [.] v -> 
         match co with 
         | c_eval t k1' _ c   => k1 = k1' -> forall v', v ~= v' -> EAM.dec t c v'
         | c_apply k1' _ c v0 => k1 = k1' -> forall v', v ~= v' -> EAM.decctx v0 c v'
         end); intros.
    apply (H _ H0)...

    dependent induction H;

    let rec rc := first 
        [ econstructor 1; eauto; rc 
        | econstructor 2; eauto; rc 
        | econstructor 3; eauto; rc 
        | econstructor 4; eauto; rc
        | intro; assert (dec_term t k1 = in_dead); 
          [ eapply dec_term_from_dead; eauto | congruence] 
        | intro; assert (dec_context ec k1 v0 = in_dead); 
          [ eapply dec_context_from_dead; eauto; apply death_propagation; auto 
          | congruence ] ]
    in 
    dependent destruction H; intros; dep_subst; try solve [rc].
  Qed.
  Hint Resolve transDecEam.


  Lemma evalMachineEam : forall {t v}, AM.eval t v -> EAM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    constructor.
    apply transDecEam...
  Qed.
  Hint Resolve evalMachineEam.


  Theorem eval_apply_correct : forall {t} {v : value init_ckind}, 
                                   RS.RS.eval t v <-> AM.eval t v.
  Proof with auto.
    intros t v; rewrite EAM.evalEam; split...
  Qed.


  Module DEC := DEC.

End ProperEAMachine.



Module PushEnterMachine (R : RED_LANG) (PRS : PE_REF_SEM R) (*<: PUSH_ENTER_MACHINE R*).

  Import R.
  Import PRS.
  Export DEC.

  Module EAM := EvalApplyMachine R RefSem.
  Module PR  := Red_Sem_Proper R PRS.RefSem.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | dec_r    : forall t {t0 k1 k2} {c : context k1 k2} {r v},
                 dec_term t k2 = in_red r -> contract r = Some t0 -> dec t0 c v ->
                 dec t c v
  | dec_val  : forall t {k} {v : value k},
                 dec_term t k = in_val v ->
                 dec t [.] v
  | dec_v_t  : forall t ec {t0 ec0} {k1 k2} {c : context k1 k2} {v v0},
                 dec_term t (k2+>ec) = in_val v -> 
                 dec_context ec k2 v = in_term t0 ec0 -> 
                 dec t0 (ec0=:c) v0 ->
                 dec t (ec=:c) v0
  | dec_red  : forall t ec {t0} {k1 k2} {c : context k1 k2} {v v0 r},
                 dec_term t (k2+>ec) = in_val v ->
                 dec_context ec k2 v = in_red r -> 
                 contract r = Some t0 -> 
                 dec t0 c v0 ->
                 dec t (ec=:c) v0
  | dec_rec  : forall t {t0 ec} {k1 k2} {c : context k1 k2} {v},
                 dec_term t k2 = in_term t0 ec ->
                 dec t0 (ec=:c) v ->
                 dec t c v.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [.] v -> eval t v.


  Lemma decEamPem : forall {t k1 k2} {c : context k1 k2} {v}, EAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v) => dec t c v)
    (P0:= fun _ v _ c v0 (_ : EAM.decctx v c v0) =>
      match c in context _ k2' return value k2' -> Prop with
      | [.] => fun v => dec v [.] v0
      | ccons ec _ c => fun v => forall d, dec_context ec _ v = d ->
        match d with
        | in_red r => forall t, contract r = Some t -> dec t c v0
        | in_term t ec0 => dec t (ec0=:c) v0
        | in_val v => False
        | in_dead => False
        end
      end v); intros; simpl.
    (* Case 1 *)
    econstructor...
    (* Case 2 *)
    dependent destruction d; subst.
    (* Case 2.1 *)
    constructor...
    (* Case 2.2 *)
    econstructor 4...
    apply (IHdec (in_red r))...
    (* Case 2.3 *)
    contradict (dec_context_not_val _ _ _ H).
    (* Case 2.4 *)
    econstructor 3...
    apply (IHdec (in_term t0 ec0))...
    (* Case 3 *)
    econstructor 5...
    (* Case 4 *)
    constructor; apply dec_term_value...
    (* Case 5 *)
    rewrite e in H0; inversion H0; subst; intros.
    rewrite e0 in H0; inversion H0; subst...
    (* Case 7 *)
    contradict (dec_context_not_val _ _ _ e).
    (* Case 8 *)
    rewrite e in H0; subst...
  Qed.


  Lemma evalEamPem : forall {t v}, EAM.eval t v -> eval t v.
  Proof.
    intros t v H; dependent destruction H; constructor; apply decEamPem; auto.
  Qed.
  Hint Resolve evalEamPem.


  Lemma decPemEam : forall {t k1 k2} {c : context k1 k2} {v}, dec t c v -> EAM.dec t c v.
  Proof with eauto.
    induction 1; intros; simpl; auto.
    econstructor 1...
    econstructor 2... econstructor... 
        intro H0; rewrite (dec_term_from_dead t _ H0) in H; discriminate.
    econstructor 2... econstructor 4...
    econstructor 2... econstructor 2...
    econstructor 3...
  Qed.


  Lemma evalPemEam : forall {t v}, eval t v -> EAM.eval t v.
  Proof.
    intros t v H; dependent destruction H; constructor; apply decPemEam; auto.
  Qed.
  Hint Resolve evalPemEam.


  Theorem evalPem : forall {t v}, PRS.RefSem.RS.eval t v <-> eval t v.
  Proof.
    intros t v; rewrite EAM.evalEam; split; auto.
  Qed.


  Module DEC := DEC.

  Definition dec_context_not_val := dec_context_not_val.
  Definition dec_term_value      := @dec_term_value.

End PushEnterMachine.



Module ProperPEMachine (R : RED_LANG) (PRS : PE_REF_SEM R) (*<: PROPER_PE_MACHINE R*).

  Import R.
  Import PRS.
  Export DEC.

  Module PEM := PushEnterMachine R PRS.


  Inductive configuration : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> configuration
  | c_final : forall {k}, value k                   -> configuration.

  Definition c_init t := c_eval t (@empty init_ckind).

  Reserved Notation " a → b " (at level 40, no associativity).


  Inductive transition : configuration -> configuration -> Prop :=
  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : value k},
               dec_term t k = in_val v ->
               c_eval t [.](k) → c_final v
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
  where " a →  b " := (transition a b).


  Module AM : ABSTRACT_MACHINE
    with Definition term          := term
    with Definition value         := value init_ckind
    with Definition configuration := configuration
    with Definition transition    := transition
    with Definition c_init        := c_init
    with Definition c_final       := @c_final init_ckind.

    Definition term          := term.
    Definition value         := value init_ckind.
    Definition configuration := configuration.
    Definition transition    := transition.
    Definition c_init        := c_init.
    Definition c_final       := @c_final init_ckind .


    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall {c0 c1},    transition c0 c1 -> trans_close c0 c1
    | multi_step : forall {c0 c1 c2}, transition c0 c1 -> 
                                          trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall {t v}, trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).


  Lemma decPemTrans : forall {t} {k1 k2} {c : context k1 k2} {v}, 
                          PEM.dec t c v -> c_eval t c →+ c_final v.
  Proof with eauto.
    induction 1; intros;
    solve 
    [ do 2 constructor; auto
    | econstructor 2; eauto; econstructor; eauto ].
  Qed.
  Hint Resolve decPemTrans.


  Lemma evalPemMachine : forall {t v}, PEM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    constructor.
    apply decPemTrans...
  Qed.
  Hint Resolve evalPemMachine.


  Lemma transDecPem : forall {t k1 k2} {c : context k1 k2} {v}, 
                          c_eval t c →+ c_final v -> PEM.dec t c v.
  Proof with eauto.
    intros.
    dependent induction H;

    dependent destruction H.

    apply PEM.dec_val...
    eapply PEM.dec_r...
    do 2 dependent destruction H0.
    eapply PEM.dec_red...
    eapply PEM.dec_v_t...
    eapply PEM.dec_rec...
  Qed.
  Hint Resolve transDecPem.


  Lemma evalMachinePem : forall {t v}, AM.eval t v -> PEM.eval t v.
  Proof with auto.
    intros.
    constructor.
    destruct H.
    apply transDecPem...
  Qed.
  Hint Resolve evalMachinePem.


  Theorem push_enter_correct : forall {t v}, PRS.RefSem.RS.eval t v <-> AM.eval t v.
  Proof.
    intros t v; rewrite (PEM.evalPem); split; auto.
  Qed.


  Module DEC := DEC.

  Definition dec_context_not_val := dec_context_not_val.
  Definition dec_term_value      := @dec_term_value.

End ProperPEMachine.