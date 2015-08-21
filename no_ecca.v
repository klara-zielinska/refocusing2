Require Import Util.
Require Import Program.
Require Import refocusing_lang.
Require Import refocusing_lang_facts.



Module no_ECCa <: RED_LANG.

  Parameter var : Set.


  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr.
  Definition term := expr.


  Inductive ck := C | ECa | CBot.
  Definition ckind := ck.


  Inductive val : ckind -> Type :=

  | vCLam   : var -> val C -> val C
  | vCVar   : var -> val C
  | vCApp   : valCa -> val C -> val C
  
  | vECaLam : var -> term -> val ECa
  | vECaVar : var -> val ECa
  | vECaApp : valCa -> val C -> val ECa
  
  | vCBot   : term -> val CBot
  
  with valCa :=

  | vCaVar : var -> valCa
  | vCaApp : valCa -> val C -> valCa.
  
  Definition value := val.


  Inductive red : ckind -> Type :=
  | rCApp   : var -> term -> term -> red C
  | rECaApp : var -> term -> term -> red ECa.
  Definition redex := red.


  Inductive ec :=
  | lam_c : var -> ec
  | ap_r  : term -> ec
  | ap_l  : valCa -> ec.
  Definition elem_context := ec.


  Definition ckind_trans (k : ckind) (ec : elem_context) := 
      match k with
      | C    => match ec with lam_c _ => C    | ap_r _ => ECa | ap_l _ => C end
      | ECa  => match ec with lam_c _ => CBot | ap_r _ => ECa | ap_l _ => C end
      | _    => CBot
      end.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).


  Definition init_ckind : ckind     :=  C.
  Definition dead_ckind (k : ckind) :=  k = CBot.

  Hint Unfold dead_ckind.


  Lemma death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).

  Proof.
    intros k H.
    destruct k;
    inversion H;
    reflexivity.
  Qed.
  
  
  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix "=:"          := ccons (at level 60, right associativity).
  
  
  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vCLam x v => Lam x (value_to_term v)
      | vCVar x => Var x
      | vCApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      | vECaLam x t => Lam x t
      | vECaVar x => Var x
      | vECaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      | vCBot t => t
      end

  with valCa_to_term v : term :=
      match v with
      | vCaVar x => Var x
      | vCaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valCa_to_term : valCa >-> term.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rCApp x t1 t2   => App (Lam x t1) t2
      | rECaApp x t1 t2 => App (Lam x t1) t2
      end.
  Coercion redex_to_term : redex >-> term.


  Scheme val_Ind   := Induction for val Sort Prop
    with valCa_Ind := Induction for valCa Sort Prop.


  Lemma value_to_term_injective : 
      forall k (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    induction v using val_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa,   valCa_to_term v = valCa_to_term v' -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma valCa_to_term_injective : 
      forall v v', valCa_to_term v = valCa_to_term v' -> v = v'.

  Proof with auto.
    induction v using valCa_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa,   valCa_to_term v = valCa_to_term v' -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma redex_to_term_injective : 
      forall k (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct k;

    solve
    [ induction r; 
      dependent destruction r'; 
      inversion H;
      f_equal; auto ].
  Qed.


  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


  Definition elem_plug (t : term) (ec : elem_context) : term :=
      match ec with
      | lam_c x => Lam x t
      | ap_r tr => App t tr
      | ap_l v  => App (v : term) t
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Lemma elem_plug_injective1 : forall ec {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.
  Proof.
    intros ec t0 t1 H.
    destruct ec;
    ( injection H; trivial ).
  Qed.


  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec ec t := exists t', ec:[t'] = t. 


  Parameter subst : var -> term -> term -> term.

  (*Import Arith.Peano_dec.
  Fixpoint subst x ex e :=
  match e with
  | Z  => Z
  | S e1 => S (subst x ex e1)
  | App e1 e2 => App (subst x ex e1) (subst x ex e2) 
  | Var y => if eq_nat_dec y x then ex else Var y
  | Lam y e1 => if eq_nat_dec y x then Lam y e1 else Lam y (subst x ex e1)
  | Case e0 e1 y e2 => Case (subst x ex e0) (subst x ex e1) y 
                          (if eq_nat_dec y x then e2 else (subst x ex e2)) 
  | Letv y e1 e2 => Letv y (subst x ex e1) (if eq_nat_dec y x then e2 else subst x ex e2)
  | Fix y e1 => if eq_nat_dec y x then Fix y e1 else Fix y (subst x ex e1)
  | Pair e1 e2 => Pair (subst x ex e1) (subst x ex e2)
  | Fst e1 => Fst (subst x ex e1)
  | Snd e1 => Snd (subst x ex e1)
  end.*)


  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rCApp   x t tx => Some (subst x tx t)
      | rECaApp x t tx => Some (subst x tx t)
      end.


  Inductive decomp (k : ckind) : Set :=
  | d_red : forall k', redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.


  Definition decomp_to_term {k} (d : decomp k) : term :=
      match d with
      | d_val v => value_to_term v
      | d_red _ r c0 => c0[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition only_empty t k := 
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k).

  Definition only_trivial t k := 
      forall t' {k'} (c : context k k'),  c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.


  Lemma valCa_is_valECa : 
      forall v1 : valCa, exists v2 : value ECa, valCa_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vECaVar v)...
    - exists (vECaApp v1 v)...
  Qed.


  Lemma value_trivial : forall {k} (v : value k), only_trivial v k.
  Proof.
    intros k1 v t k2 c; revert t.
    induction c.

    - intuition.

    - intros t H H0.
      right.

      destruct IHc with (ec0:[t]) as [(H1, H2) | (v0, H1)];
          try solve [ auto using death_propagation ];
          dep_subst;
      [ destruct ec0; destruct v;  dependent destruction H
      | destruct ec0; destruct v0; dependent destruction H1 ];

      solve
      [ eautof | apply valCa_is_valECa ].
  Qed.


  Lemma value_redex : forall k (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v; 
    simpl;
    try match goal with 
    | |- App (valCa_to_term ?v) _ <> _ => dependent_destruction2 v
    end;
    
    solve [ discriminate ].
  Qed.


  Lemma ot_subterm_val : 
      forall t t0 ec k, only_trivial t k -> ec:[t0] = t -> ~ dead_ckind (k+>ec) ->
          exists v : value (k+>ec), t0 = v.

  Proof with auto.
    intros t t0 ec k H H0 H1.
    destruct (H t0 _ (ec =: [.])) as [(?, H3) | (v, ?)]...
    - discriminateJM H3.
    - exists v; destruct k...
  Qed.


  Lemma plug_compose  : 
      forall {k1 k2 k3} (c0 : context k1 k2) (c1 : context k3 k1) t, 
          (c0 ~+ c1)[t] = c1[c0[t]].
  Proof.
    induction c0; intros.
    - auto.
    - apply IHc0.
  Qed.


  Lemma ot_propagation : 
      forall t ec k, only_trivial ec:[t] k -> only_trivial t (k+>ec).

  Proof with eauto.
    intros t ec k H.
    intros t' k' c H1 H2.
    destruct (H t' _ (c ~+ ec =: [.])) as [(?, H3) | ?]... 
    - rewrite plug_compose; subst...
    - destruct c; discriminateJM H3.
  Qed.


  Lemma trivial_val_red : 
      forall k t, only_trivial t k ->
          (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).

  Proof with (simpl; eautof).
    intros k t H.
    induction t;
        destruct k.
    
    - destruct (ot_subterm_val _ t1 (ap_r t2) _ H) as (v, H0)...
      subst.
      simpl in v; dependent destruction v.
      + right; eexists (rCApp _ _ _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaVar v)) _ H) as (v0, H0)...
        subst.
        left; eexists (vCApp (vCaVar _) _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaApp v v1)) _ H) as (v0, H0)...
        subst.
        left; eexists (vCApp (vCaApp _ _) _)...

      (* almost "copy-past" of the previous case *)
    - destruct (ot_subterm_val _ t1 (ap_r t2) _ H) as (v, H0)...
      subst.
      simpl in v; dependent destruction v.
      + right; eexists (rECaApp _ _ _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaVar v)) _ H) as (v0, H0)...
        subst.
        left; eexists (vECaApp (vCaVar _) _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaApp v v1)) _ H) as (v0, H0)...
        subst.
        left; eexists (vECaApp (vCaApp _ _) _)...

    - left; eexists (vCBot (App _ _))...

    - left; eexists (vCVar _)...

    - left; eexists (vECaVar _)...

    - left; eexists (vCBot (Var _))...

    - destruct (ot_subterm_val _ t (lam_c v) _ H)...
      subst.
      left; eexists (vCLam _ _); subst...

    - left; eexists (vECaLam _ _)...

    - left; eexists (vCBot (Lam _ _))...
  Qed.


  Lemma dead_context_dead : 
      forall {k1 k2}, context k1 k2 -> dead_ckind k1 -> dead_ckind k2.

  Proof with auto.
    intros ? ? c H; revert c.
    induction 1.
    - trivial.
    - apply death_propagation...
  Qed.


  Lemma proper_death : forall k, dead_ckind k -> 
                           ~ exists k' (c : context k k') (r : redex k'), True.
  Proof with eauto.
    intros k H H0.
    destruct k;

    (*1*)try solve [discriminate H].

    (*2*)destruct H0 as (k', (c, (r, _))).
         assert (dead_ckind k').
         + eapply dead_context_dead...
         + dependent destruction r; 
           discriminate H0.
  Qed.

End no_ECCa.



Module no_ECCa_Ref <: RED_REF_LANG.

  Module R  := no_ECCa.
  Module RF := RED_LANG_Facts R.
  Export R.
  Import RF.


  Module DEC <: DEC_STEP R.

    Inductive interm_dec k : Set :=
    | in_red  : redex k -> interm_dec k
    | in_term : term -> elem_context -> interm_dec k
    | in_val  : value k -> interm_dec k
    | in_dead : interm_dec k.
    Arguments in_red {k} _.    Arguments in_val {k} _.
    Arguments in_term {k} _ _. Arguments in_dead {k}.


    Definition dec_term t k : interm_dec k :=

        match k as k0 return interm_dec k0 with 
        | C    => match t with
                  | App t1 t2 => in_term t1 (ap_r t2)
                  | Var x     => in_val (vCVar x)
                  | Lam x t1  => in_term t1 (lam_c x)
                  end
        | ECa  => match t with
                  | App t1 t2 => in_term t1 (ap_r t2)
                  | Var x     => in_val (vECaVar x)
                  | Lam x t1  => in_val (vECaLam x t1)
                  end
        | CBot => in_dead
        end.


    Definition dec_context ec k (v : value (k+>ec)) : interm_dec k :=

        match ec as ec0 return value (k+>ec0) -> interm_dec k with

        | lam_c x  => match k as k0 return value (k0+>lam_c x) -> interm_dec k0 with
                      | C    => fun v => in_val (vCLam x v)
                      | ECa  => fun v => in_dead
                      | CBot => fun v => in_dead
                      end

        | ap_r t   => match k as k0 return value (k0+>(ap_r t)) -> interm_dec k0 with
                      | C    => fun v => 
                                    match v with
                                    | vECaLam x t0  => in_red (rCApp x t0 t)
                                    | vECaVar x     => in_term t (ap_l (vCaVar x))
                                    | vECaApp v1 v2 => in_term t (ap_l (vCaApp v1 v2))
                                    | _ => @in_dead C
                                    end
                      | ECa  => fun v => 
                                    match v with
                                    | vECaLam x t0  => in_red (rECaApp x t0 t)
                                    | vECaVar x     => in_term t (ap_l (vCaVar x))
                                    | vECaApp v1 v2 => in_term t (ap_l (vCaApp v1 v2))
                                    | _ => @in_dead ECa
                                    end
                      | CBot => fun v => in_dead
                      end

        | ap_l v0  => match k as k0 return value (k0+>(ap_l v0)) -> interm_dec k0 with
                      | C    => fun v => in_val (vCApp v0 v)
                      | ECa  => fun v => in_val (vECaApp v0 v)
                      | CBot => fun v => in_dead
                      end
        end v.


    Lemma dec_term_correct : 
        forall (t : term) k, match dec_term t k with
        | in_red r      => t = r
        | in_val v      => t = v
        | in_term t' ec => t = ec:[t']
        | in_dead       => dead_ckind k 
        end.

    Proof.
      destruct k, t; simpl; 
      auto.
    Qed.


    Lemma dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead.
    Proof.
      intros.
      destruct k;
      solve [ autof ].
    Qed.


    Lemma dec_term_next_alive : 
        forall t k t0 ec0, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

    Proof.
      intros t k t0 ec0 H.
      destruct t, k;
      solve [ inversion H; subst; 
              auto ].
    Qed.


    Lemma dec_context_correct : 
        forall ec k v, match dec_context ec k v with
        | in_red r      => ec:[v] = r
        | in_val v'     => ec:[v] = v'
        | in_term t ec' => ec:[v] = ec':[t]
        | in_dead       => dead_ckind (k+>ec)
        end.

    Proof.
      intros.
      destruct k, ec0; dependent destruction v;
      simpl;
      solve [ auto ].
    Qed.


    Lemma dec_context_from_dead : forall ec k v, 
        dead_ckind (k+>ec) -> dec_context ec k v = in_dead.

    Proof.
      intros.
      destruct ec0, k;
      solve [ autof ].
    Qed.


    Lemma dec_context_next_alive : forall ec k v {t ec0}, 
        dec_context ec k v = in_term t ec0 -> ~ dead_ckind (k+>ec0).

    Proof.
      intros.
      destruct ec0, ec1, k; dependent destruction v;  
      solve [ autof ].
    Qed.

  End DEC.

  Export DEC.



  Lemma redex_trivial : forall k (r : redex k), only_trivial r k.
  Proof with auto.
    intros k1 r t k2 c; revert t.
    induction c.
    - intuition.
    - intros.
      right.

      destruct IHc with (ec0:[t]) as [(H1, H2) | (v0, H1)];
          try solve [auto using death_propagation];
          dep_subst; simpl in *;
      match goal with
      | [Hvr : ec0 :[ t ] = _ ?vr |- _] => 
            destruct ec0; destruct vr; dependent_destruction2 Hvr
      end;

      solve 
      [ eautof 
      | apply valCa_is_valECa
      | eexists (vECaLam _ _); simpl; auto 
      | dependent destruction v; discriminate ].
  Qed.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec, t = ec:[t0] -> subterm_one_step t0 t.


  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    RED_REF_LANG_Help.prove_st_wf.
  Qed.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Definition ec_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match k with
      | CBot => False
      | _      => match ec, ec0 with 
                  | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
                  | _, _           => False
                  end
      end.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).


  Lemma wf_eco : forall k t, well_founded (ec_order k t).
  Proof.
    RED_REF_LANG_Help.prove_ec_wf.
  Qed.


  Lemma dec_term_red_empty : 
      forall t k (r : redex k), dec_term t k = in_red r -> only_empty t k.

  Proof with auto.
    intros t k r H.
    destruct t; 
    inversion H; subst; clear H;

    solve
    [ intros t0 k' c H H0; generalize dependent t0;

      induction c;
      intros; simpl in *;
      [ intuition
      | destruct (IHc (death_propagation2 _ _ H0) _ H);
        dep_subst;
        destruct k2, ec0;
        solve [inversion H1; auto] 
    ] ].
  Qed.


  Lemma dec_term_val_empty : forall t k (v : value k), 
                                 dec_term t k = in_val v -> only_empty t k.
  Proof with auto.
    intros t k v H.
    destruct t;
    intros t0 k' c H0 H1; generalize dependent t0;
    solve
    [ induction c;
      intros t0 H0; simpl in *;
      [ intuition
      | destruct (IHc (death_propagation2 _ _ H1) _ H0); dep_subst;
        simpl in H;
        destruct k2, ec0; 
        inversion H; subst; 
        solve [discriminate H | autof] 
    ] ].
  Qed.


  Lemma dec_term_term_top : forall t k {t' ec}, 
            dec_term t k = in_term t' ec -> forall ec', ~ k, t |~ ec << ec'.

  Proof.
    intros t k t' ec H ec' H0.
    destruct k, t, ec'; 
    solve [ inversion H; subst; inversion H0 ].
  Qed.


  Lemma ec_order_comp_fi :
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
          ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

  Proof with auto.
    intros k t ec0 ec1 H.
    destruct k, ec0, ec1;
    inversion H;
    solve [auto].
  Qed.


  Lemma elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

  Proof.
    intros t ec0 t' H k ec' H0.
    subst.

    destruct k, ec0, ec'; autof;
    unfold ec_order in H0; destruct H0 as (H, _);
    destruct (valCa_is_valECa v) as (v0, H0);

    solve
    [ exists v0;
      simpl; rewrite <- H0;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.


  Lemma dec_context_red_bot : 
      forall k ec v r, dec_context ec k v = in_red r -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;
    solve
    [ autof
    | inversion H;
      intro G;
      unfold ec_order in G; destruct G as (G, _);
      destruct G as (t1, G); inversion G; subst;
      destruct v0; 
      autof ].
  Qed.


  Lemma dec_context_val_bot : 
      forall k ec v v', dec_context ec k v = in_val v' -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k ec v v' H ec'.
    destruct k, ec, ec'; dependent destruction v; 
    solve [ autof ].
  Qed.


  Lemma eco_antirefl : forall k t ec, ~ k, t |~ ec << ec.
  Proof.
    intros k t ec.
    destruct k, ec; 
    solve [ auto ].
  Qed.


  Lemma ec_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Proof.
    intros k t ec ec0 H.
    destruct k, ec, ec0;
    solve [ autof ].
  Qed.


  Lemma ec_order_trans :  forall k t ec0 ec1 ec2, 
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 -> 
      k,t |~ ec0 << ec2.

  Proof.
    intros k t ec0 ec1 ec2 H H0.
    destruct k, ec0, ec1;
    solve [ autof ].
  Qed.


  Lemma dec_context_term_next : 
      forall ec0 k v t ec1, dec_context ec0 k v = in_term t ec1 ->
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.

  Proof.
    intros ec0 k v t ec1 H.
    destruct k, ec0, ec1; dependent destruction v; 
    solve 
    [ autof

    | inversion H; subst;
      split;
      [ constructor; 
        compute; eauto
      | intros ec'' H0 H1; 
        destruct ec'';
        solve [ autof ] 
      ] ].
  Qed.


  Lemma ec_order_comp_if : forall t ec0 ec1, 
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k,t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ec0 = ec1.

  Proof.
    intros t ec0 ec1 H0 H1 k H2 H3.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5).
    subst t.
    destruct k, ec0, ec1;
    inversion H5; subst;

    solve
    [ compute; eautof 7
    | do 2 right; 
      f_equal;
      apply valCa_to_term_injective; auto ].
  Qed.

End no_ECCa_Ref.

