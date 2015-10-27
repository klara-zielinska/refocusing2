Require Import Util.
Require Import Program.
Require Import refocusing_lang.
Require Import reduction_semantics_facts.


Open Scope list.


Module no_es_cl_ECCa <: RED_LANG.

  Require Export Peano_dec Compare_dec.


  Inductive term0 :=
  | Var0   : nat            -> term0
  | Lam0   : term0          -> term0
  | App0   : term0 -> term0 -> term0.


  Inductive closure : Set :=
  | Cl : term0 -> list (nat * substitut) -> closure

  with substitut : Set :=
  | Sub  : closure -> substitut
  | Lift : nat     -> substitut.

  Notation env    := (list (nat * substitut)).
  Notation "t @ s" := (Cl t s) (at level 10).


  Inductive __term : Set := 
  | Var   : nat     -> __term
  | Lam   : __term  -> __term
  | App   : __term  -> __term -> __term
  | Cl_t  : closure -> __term
  | OpVar : nat -> env -> nat -> __term.
  Definition term := __term.
  Hint Unfold term.


  Fixpoint term0_to_term t0 : term :=
      match t0 with 
      | Var0 i     => Var i 
      | Lam0 t     => Lam (term0_to_term t) 
      | App0 t1 t2 => App (term0_to_term t1) (term0_to_term t2) 
      end.
  Coercion term0_to_term : term0 >-> term.

  Coercion closure_to_term cl : term := Cl_t cl.


  Inductive ck := C | ECa | CBot.
  Definition ckind := ck.
  Hint Unfold ckind.

  Definition CECa (k : ckind) := match k with CBot => False | _ => True end.


  Definition init_ckind : ckind     :=  C.
  Definition dead_ckind (k : ckind) :=  k = CBot.
  Hint Unfold init_ckind dead_ckind.


  Inductive val : ckind -> Type :=

  | vCLam   : val C -> val C
  | vCVar   : nat -> val C
  | vCApp   : valCa -> val C -> val C
  
  | vECaLam    : term -> val ECa
  | vECaLam_cl : term0 -> env -> val ECa
  | vECaCa     : valCa -> val ECa
  
  with valCa : Set :=

  | vCaVar : nat -> valCa
  | vCaApp : valCa -> val C -> valCa.

  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val Sort Prop
    with valCa_Ind := Induction for valCa Sort Prop.


  Fixpoint valueC_to_term0 (v : value C) : term0 :=
      match v with
      | vCLam v     => Lam0 (valueC_to_term0 v) 
      | vCVar i     => Var0 i
      | vCApp v1 v2 => App0 (valCa_to_term0 v1) (valueC_to_term0 v2)
      end

  with valCa_to_term0 v : term0 :=
      match v with
      | vCaVar i     => Var0 i
      | vCaApp v1 v2 => App0 (valCa_to_term0 v1) (valueC_to_term0 v2)
      end.
  Coercion valCa_to_term0 : valCa >-> term0.

  Definition value_to_term {k} : value k -> term :=
      match k as k return value k -> term with
      | C    => fun v => valueC_to_term0 v
      | ECa  => fun v => match v with
                         | vECaLam t      => Lam t
                         | vECaLam_cl t e => Cl (Lam0 t) e 
                         | vECaCa v'      => valCa_to_term0 v'
                         end
      | CBot => fun v => match v with end
      end.
  Coercion value_to_term : value >-> term.

(*
  Definition vVar n k : value k := 
      match k with 
      | C => vCVar n | ECa => vECaVar n 
      | CBot => vCBot (Var n) 
      end.*)


  Definition not_closure (t : term) := match t with Cl_t _ => False | _ => True end.

  Inductive red : ckind -> Type :=
  | rAppLam    : forall k, CECa k -> term -> term -> red k
  | rAppLam_cl : forall k, CECa k -> term0 -> env -> term -> red k

  | rSubVar : forall k, CECa k -> nat            -> env -> red k
  | rSubVarOp : forall k, CECa k -> nat            -> env -> nat -> red k
  | rSubLam :                     term0          -> env -> red C
  | rSubApp : forall k, CECa k -> term0 -> term0 -> env -> red k.
  Definition redex := red.
  Hint Unfold redex.


  Definition redex_to_term {k} (r : redex k) : term := 
      match r with
      | rAppLam _ _ t1 t2        => App (Lam t1) (t2 : term)
      | rAppLam_cl _ _  t0 e t2  => App (Cl (Lam0 t0) e : term) t2

      | rSubVar _ _ i     e   => Cl (Var0 i) e
      | rSubVarOp _ _ i e g => OpVar i e g
      | rSubLam     t0    e   => Cl (Lam0 t0) e
      | rSubApp _ _ t1 t2 e   => Cl (App0 t1 t2) e
      end.
  Coercion redex_to_term : redex >-> term.


  Inductive ec : Set :=
  | lam_c  : ec
  | ap_r   : term -> ec
  | ap_l   : valCa -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.


  Definition elem_plug (t : term) (ec : elem_context) : term :=
      match ec with
      | lam_c   => Lam t
      | ap_r cl => App t (cl : term)
      | ap_l v  => App (v : term) t
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Definition ckind_trans (k : ckind) (ec : elem_context) := 
      match k with
      | C    => match ec with lam_c => C    | ap_r _ => ECa | ap_l _ => C end
      | ECa  => match ec with lam_c => CBot | ap_r _ => ECa | ap_l _ => C end
      | CBot => CBot
      end.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).


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


  Lemma term0_to_term_injective : 
      forall t t', term0_to_term t = term0_to_term t' -> t = t'.

  Proof.
    induction t; intros t' H; 
    destruct t'; inversion H; 
    solve [ f_equal; auto ].
  Qed.


  Lemma closure_to_term_injective :
      forall cl cl', closure_to_term cl = closure_to_term cl' -> cl = cl'.

  Proof. inversion 1; auto. Qed.

(*
  Lemma value_C_to_term_is : 
      forall v : value C, value_to_term v = term0_to_term (valueC_to_term0 v).

  Proof. dependent destruction v; auto. Qed.*)


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof.
    induction v using val_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa, valCa_to_term0 v = valCa_to_term0 v' -> v = v');
        dependent destruction v'; 
        intro H; inversion H;
        simpl in *;

    match goal with 
    | _ => solve [auto using f_equal, f_equal2, term0_to_term_injective]
    | v : valCa |- _ => destruct v; discriminate
    end.
  Qed.


  Lemma valCa_to_term0_injective : 
      forall v v', valCa_to_term0 v = valCa_to_term0 v' -> v = v'.

  Proof.
    induction v using valCa_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa, valCa_to_term0 v = valCa_to_term0 v' -> v = v');
        dependent destruction v'; 
        intro H; inversion H;
        simpl in *;

    match goal with 
    | _ => solve [auto using f_equal, f_equal2, term0_to_term_injective]
    | v : valCa |- _ => destruct v; discriminate
    end.
  Qed.


  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    intros k r r' H.
    destruct k;
    dependent destruction r; dependent destruction r';
    inversion H; subst;

    repeat match goal with 
    | H : CECa ?k |- _ => 
          try destruct k; destruct H
    | H : _ ++ _ :: _ = _ ++ _ :: _ |- _ =>
          destruct (List.app_inj_tail _ _ _ _ H) as (?, G);
          inversion G
    end;

    try solve [ f_equal; auto | destruct_all closure; autof |
destruct t1, t2; destruct n0, n; autof ].
  Qed.


  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


  Lemma elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ec t0 t1 H.
    destruct ec;
    solve
    [ inversion H; trivial ].
  Qed.


  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec ec t := exists t', ec:[t'] = t.

  Definition sub_step i j s e g :=
      if lt_dec i j then Var (i+g) else
      match s with
      | Sub (Cl t e') => if eq_nat_dec i j then Cl t ((0, Lift (g+j))::e') : term
                                           else OpVar (i-j-1) e (g+j)
      | Lift g'       => OpVar (i-j) e (g+j+g')
      end.

  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rAppLam    _ _ _ _    => None 
      | rAppLam_cl _ _ t e (Cl_t cl) => Some (Cl t ((0, Sub cl)::e) : term)
      | rAppLam_cl _ _ t e _         => None
      | rSubVar _ _ i ([])    => Some (Var i)
      | rSubVar _ _ i ((j, s)::e) => Some (sub_step i j s e 0)
      | rSubVarOp _ _ i ([]) g => Some (Var (i+g))
      | rSubVarOp _ _ i ((j, s)::e) g => Some (sub_step i j s e g)
      | rSubLam t ([])        => Some (Lam (Cl t ([]) : term))
      | rSubLam t ((j, s)::e) => Some (Lam (Cl t ((1+j, s)::e) : term))
      | rSubApp _ _ t1 t2 e   => Some (App (Cl t1 e : term) (Cl t2 e : term))
      end.


  Inductive decomp (k : ckind) : Set :=
  | d_red : forall k', redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.


  Definition decomp_to_term {k} (d : decomp k) : term :=
      match d with
      | d_val v      => value_to_term v
      | d_red _ r c0 => c0[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition only_empty t k := 
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k).

  Definition only_trivial t k := 
      forall t' {k'} (c : context k k'),  c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.

(*
  Lemma valCa_is_valECa : 
      forall v1 : valCa, exists v2 : value ECa, 
          (valCa_to_term0 v1 : term) = value_to_term v2.

  Proof with try rewrite <- value_C_to_term_is in *; auto.
    destruct v1; intros.
    - exists (vECaVar n)...
    - exists (vECaApp v1 v); simpl...
  Qed.*)


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

      try solve
      [ simpl; eautof | apply valCa_is_valECa | destruct t0; discriminate ].
eexists (vECaCa _); simpl; eauto.
destruct v; inversion x; subst.
eexists (vECaCa _); simpl; eauto.
destruct v; inversion x; subst; simpl; eauto.
eexists (vECaCa _); simpl; eauto.
destruct v0; inversion x; subst.
eexists (vECaCa _); simpl; eauto.
destruct v0; inversion x; subst. simpl; eauto.
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v; 
    simpl;
    try match goal with 
    | |- App (term0_to_term (valCa_to_term0 ?v)) _ <> _ => dependent_destruction2 v
    end;

    try solve [ discriminate | tauto ].
destruct v as [? | v v']; [| dependent_destruction2 v]; discriminate.
destruct v as [? | v v']; [| dependent_destruction2 v]; discriminate.
destruct v as [? | v v']; [| dependent_destruction2 v]; discriminate.
destruct v; discriminate.
destruct v; discriminate.
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
      forall k t, ~dead_ckind k -> only_trivial t k ->
          (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).

  Proof with simpl; eautof.
    intros k t; revert k.
    induction t;
        intros k G H;
        destruct k.

    - left; eexists (vCVar _)...

    - left; eexists (vECaCa (vCaVar _))...

    - autof.

    - destruct (ot_subterm_val _ t lam_c _ H)...
      subst.
      left; eexists (vCLam _)...

    - left; eexists (vECaLam _)...

    - autof.

    - destruct (ot_subterm_val _ t1 (ap_r t2) _ H) as (v, H0)...
      subst.
      simpl in v; dependent destruction v.
      + right; eexists (rAppLam C I _ _)...
      + right; eexists (rAppLam_cl C I _ _ _)...
      + destruct (ot_subterm_val _ t2 (ap_l v) _ H) as (v0, H0)...
        subst.
        left; eexists (vCApp _ _)...

      (* almost "copy-past" of the previous case *)
    - destruct (ot_subterm_val _ t1 (ap_r t2) _ H) as (v, H0)...
      subst.
      simpl in v; dependent destruction v.
      + right; eexists (rAppLam ECa I _ _)...
      + right; eexists (rAppLam_cl ECa I _ _ _)...
      + destruct (ot_subterm_val _ t2 (ap_l v) _ H) as (v0, H0)...
        subst.
        left; eexists (vECaCa (vCaApp _ _))...

    - autof.

    - right.
      destruct c as [[i | t | t1 t2] e].
      + eexists (rSubVar C I _ _)...
      + eexists (rSubLam _ _)...
      + eexists (rSubApp C I _ _ _)...

    - destruct c as [[i | t | t1 t2] e].
      + right; eexists (rSubVar ECa I _ _)...
      + left; eexists (vECaLam_cl _ _)...
      + right; eexists (rSubApp ECa I _ _ _)... 

    - autof.

    - right.
      eexists (rSubVarOp C I _ _ _)...

    - right.
      eexists (rSubVarOp ECa I _ _ _)...

    - autof.
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
           try match goal with
           | H : CECa ?k |- _ => try destruct k; destruct H
           end;
           solve [discriminate H0].
  Qed.


(*
  (* Contexts from the Johan Munk's paper *)
  (* To refactor *)
  Inductive ckind_IO := Aio | Cio | Dio.

  Inductive context_IO : ckind_IO -> Set :=
  | hole_io   : context_IO Aio
  | ap_l_io   : context_IO Cio -> valCa -> context_IO Aio
  | lam_c_io  : context_IO Aio -> context_IO Aio

  | a_is_c_io : context_IO Aio -> context_IO Cio
  | ap_r_io   : context_IO Cio -> term -> context_IO Cio

  | c_is_d_io : context_IO Cio -> context_IO Dio
  | stag_c_io : context_IO Dio -> sub_tag -> context_IO Dio.

  Definition a_is_d_io c := c_is_d_io (a_is_c_io c).


  Definition context_to_IO {k1 k2} (c : context k1 k2) : 
               match k2 with  
               | C => context_IO Aio | ECa => context_IO Cio 
               | D => context_IO Dio | CBot => unit
               end.
  dependent induction c.

  destruct k1.
  exact hole_io.
  exact (a_is_c_io hole_io).
  exact (a_is_d_io hole_io).
  exact ().

  remember ec0.
  destruct k2, e; simpl.
  exact (lam_c_io IHc).
  exact (ap_r_io (a_is_c_io IHc) t).
  exact (ap_l_io (a_is_c_io IHc) v).
  exact (stag_c_io (a_is_d_io IHc) s).
  exact ().
  exact (ap_r_io IHc t).
  exact (ap_l_io IHc v).
  exact (stag_c_io (c_is_d_io IHc) s).
  exact ().
  exact ().
  exact ().
  exact (stag_c_io IHc s).
  exact ().
  exact ().
  exact ().
  exact ().
  Defined.



  Definition context_from_IO {k} (c : context_IO k) : 
               match k with  
               | Aio => context C C | Cio => context C C + context C ECa 
               | Dio => context C C + context C ECa + context C D
               end.

  dependent induction c.

  exact [.].

  destruct IHc;
  exact (ap_l v=:c0).

  exact (lam_c=:IHc).

  exact (inl IHc).

  destruct IHc;
  exact (inr (ap_r t=:c0)).

  exact (inl IHc).

  destruct IHc as [[c0 | c0] | c0];
  exact (inr (stag_c s=:c0)).
  Defined.



  Lemma to_from_IO_is_id : 
            forall k (c : context_IO k),
                match k as k return context_IO k -> Prop with
                | Cio => fun c =>
                    c = match context_from_IO c with 
                    | inl c => a_is_c_io (context_to_IO c) 
                    | inr c => context_to_IO c 
                    end
                | Aio => fun c => c = context_to_IO (context_from_IO c)
                | Dio => fun c =>
                    c = match context_from_IO c with 
                    | inl (inl c) => a_is_d_io (context_to_IO c) 
                    | inl (inr c) => c_is_d_io (context_to_IO c) 
                    | inr c => context_to_IO c 
                    end
                end c.
  Proof.
    induction c; simpl;
    auto;
    try (destruct (context_from_IO c));
    try destruct s0;
    simpl; try unfold a_is_d_io in *; try congruence.
  Qed.


  Lemma from_to_IO_is_id : 
            forall k (c : context C k),
                match k as k return context C k -> Prop with
                | C => fun c => c = context_from_IO (context_to_IO c)
                | ECa => fun c => inr c = context_from_IO (context_to_IO c)
                | D => fun c => inr c = context_from_IO (context_to_IO c)
                | CBot => fun c => True
                end c.
  Proof.
    induction c. 
    simpl; auto.
    
    destruct k2, ec0; simpl; try rewrite <- IHc; try congruence; auto.
  Qed.


  Fixpoint plug_IO t {k} (c : context_IO k) :=
      match c with
      | hole_io       => t
      | ap_l_io c' v  => plug_IO (App (v : term) t) c'
      | lam_c_io c'   => plug_IO (Lam t) c'
      | a_is_c_io c'  => plug_IO t c'
      | ap_r_io c' t' => plug_IO (App t t') c'
      | c_is_d_io c'  => plug_IO t c'
      | stag_c_io c' (n, st_sub t')  => plug_IO (Sub t n t') c'
      | stag_c_io c' (n, st_shift m) => plug_IO (Shift t n m) c'
      end.


  Lemma plug_compatible : 
          forall {k1 k2} (c : context k1 k2) t,
              match k2 as k2 return context k1 k2 -> Prop with
              | CBot => fun _ => True
              | k2   => fun c => c[t] = plug_IO t (context_to_IO c) 
              end c.
  Proof.
    induction c.
    destruct k1; auto.

    destruct k2, ec0; destruct_all sub_tag; destruct_all substitut; simpl in *; auto.
  Qed.


  Lemma plug_compatible2 : 
          forall {k} (c : context_IO k) (t : term),
              plug_IO t c =
              match k as k return context_IO k -> term with
              | Aio => fun c => (context_from_IO c)[t]
              | Cio => fun c => match context_from_IO c with 
                                | inl c | inr c => c[t] end
              | Dio => fun c => match context_from_IO c with 
                                | inl (inl c) | inl (inr c) | inr c => c[t] end
              end c.
  Proof.
    intros.
    symmetry.
    destruct k.
    rewrite (to_from_IO_is_id Aio) at 2.
    apply @plug_compatible with (k2 := C).

    rewrite (to_from_IO_is_id Cio) at 2.
    destruct (context_from_IO c).
    simpl.
    apply @plug_compatible with (k2 := C).
    apply @plug_compatible with (k2 := ECa).

    rewrite (to_from_IO_is_id Dio) at 2.
    destruct (context_from_IO c) as [[c0 | c0] | c0];
    simpl.
    apply @plug_compatible with (k2 := C).
    apply @plug_compatible with (k2 := ECa).
    apply @plug_compatible with (k2 := D).
  Qed.
  *)

End no_es_cl_ECCa.




Module no_es_cl_ECCa_Ref <: RED_REF_LANG.

  Module R  := no_es_cl_ECCa.
  Module RF := RED_LANG_Facts R.
  Export R.
  Import RF.


  Module DEC <: REF_STEP R.

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
                  | App t1 t2   => in_term t1 (ap_r t2)
                  | Var i       => in_val (vCVar i)
                  | Lam t1      => in_term t1 lam_c
                  | Cl_t (Cl (Var0 i) e)     => in_red (rSubVar C I i e)
                  | Cl_t (Cl (Lam0 t) e)     => in_red (rSubLam t e)
                  | Cl_t (Cl (App0 t1 t2) e) => in_red (rSubApp C I t1 t2 e)
                  | OpVar i e g => in_red (rSubVarOp C I i e g)
                  end
        | ECa  => match t with
                  | App t1 t2 => in_term t1 (ap_r t2)
                  | Var i     => in_val (vECaCa (vCaVar i))
                  | Lam t1    => in_val (vECaLam t1)
                  | Cl_t (Cl (Var0 i) e)     => in_red (rSubVar ECa I i e)
                  | Cl_t (Cl (Lam0 t) e)     => in_val (vECaLam_cl t e)
                  | Cl_t (Cl (App0 t1 t2) e) => in_red (rSubApp ECa I t1 t2 e)
                  | OpVar i e g   => in_red (rSubVarOp ECa I i e g)
                  end
        | CBot => in_dead
        end.


    Definition dec_context ec k : value (k+>ec) -> interm_dec k :=

        match ec as ec, k as k return value (k+>ec) -> interm_dec k with

        | lam_c, C      => fun v => in_val (vCLam v)
        | lam_c, ECa    => fun _ => in_dead
        | lam_c, CBot   => fun _ => in_dead

        | ap_r t, C     => fun v => 
                               match v with
                               | vECaLam t0      => in_red (rAppLam C I t0 t)
                               | vECaLam_cl t0 e => in_red (rAppLam_cl C I t0 e t)
                               | vECaCa v        => in_term t (ap_l v)
                               | _ => @in_dead C
                               end
        | ap_r t, ECa   => fun v => 
                               match v with
                               | vECaLam t0      => in_red (rAppLam ECa I t0 t)
                               | vECaLam_cl t0 e => in_red (rAppLam_cl ECa I t0 e t)
                               | vECaCa v        => in_term t (ap_l v)
                               | _ => @in_dead ECa
                               end
        | ap_r t, CBot  => fun _ => in_dead
       

        | ap_l v0, C    => fun v => in_val (vCApp v0 v)
        | ap_l v0, ECa  => fun v => in_val (vECaCa (vCaApp v0 v))
        | ap_l v0, CBot => fun _ => in_dead

        end.


    Lemma dec_term_correct : 
        forall (t : term) k, match dec_term t k with
        | in_red r      => t = r
        | in_val v      => t = v
        | in_term t' ec => t = ec:[t']
        | in_dead       => dead_ckind k 
        end.

    Proof.
      destruct k, t; 
      try match goal with c : closure |- _ => 
          destruct c as [t0]; destruct t0 
      end; 
      solve [ simpl; auto ].
    Qed.


    Lemma dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead.
    Proof.
      intros t k H.
      destruct k;
      solve [ autof ].
    Qed.


    Lemma dec_term_next_alive : 
        forall t k t0 ec0, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

    Proof.
      intros t k t0 ec0 H.

      destruct t, k;
      try match goal with c : closure |- _ => 
          destruct c as [tt0]; destruct tt0 
      end;
          inversion H; subst; 

      solve [ auto ].
    Qed.


    Lemma dec_context_correct : 
        forall ec k v, match dec_context ec k v with
        | in_red r      => ec:[v] = r
        | in_val v'     => ec:[v] = v'
        | in_term t ec' => ec:[v] = ec':[t]
        | in_dead       => dead_ckind (k+>ec)
        end.

    Proof.
      intros ec k v.
      destruct k, ec; dependent destruction v;
      simpl;
      solve [ auto ].
    Qed.


    Lemma dec_context_from_dead : forall ec k v, 
        dead_ckind (k+>ec) -> dec_context ec k v = in_dead.

    Proof.
      intros ec k v H.
      destruct ec, k;
      solve [ autof ].
    Qed.


    Lemma dec_context_next_alive : forall ec k v {t ec0}, 
        dec_context ec k v = in_term t ec0 -> ~ dead_ckind (k+>ec0).

    Proof.
      intros ec k v t ec0 H.
      destruct ec, ec0, k; dependent destruction v;  
      solve [ autof ].
    Qed.

  End DEC.

  Export DEC.


  Lemma redex_trivial : forall {k} (r : redex k), only_trivial r k.
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
      | Hvr : ec0 :[ t ] = _ ?vr |- _ => 
            destruct ec0; destruct vr; 
            simpl in Hvr;
            try match type of Hvr with _ = _ (valCa_to_term0 ?v) => destruct v end;
            dependent_destruction2 Hvr
      end;
      try match goal with
      | H : CECa ?k |- _ => try destruct k; destruct H
      end;

      try solve 
      [ simpl; eautof 
      | apply valCa_is_valECa
      | eexists (vECaLam _); simpl; auto 
      | eexists (vECaLam_cl _ _); simpl; auto 
      | eexists (vECaCa _); simpl; auto 
      | dependent destruction v; discriminate ].
  Qed.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec, t = ec:[t0] -> subterm_one_step t0 t.


  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    RED_REF_LANG_Help.prove_st_wf;

    inversion H1; dep_subst; 
    auto.
  Qed.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Definition ec_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match k with
      | CBot => False
      | _    => match ec, ec0 with 
                | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
                | _, _           => False
                end
      end.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).


  Lemma wf_eco : forall k t, well_founded (ec_order k t).
  Proof.
    RED_REF_LANG_Help.prove_ec_wf.
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

    try solve
    [ compute; eautof 7
    | do 2 right; 
      f_equal;
      auto using valCa_to_term0_injective, term0_to_term_injective ].
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


  Lemma dec_term_red_empty : 
      forall t k (r : redex k), dec_term t k = in_red r -> only_empty t k.

  Proof with auto.
    intros t k r H.
    destruct t, k; destruct_all closure;
    try match goal with t0 : term0 |- _ => destruct t0 end;
    inversion H; subst; clear H;

    try solve
    [ intros t0 k' c H H0; generalize dependent t0;

      induction c;
      intros; simpl in *;
      [ intuition
      | destruct (IHc (death_propagation2 _ _ H0) _ H);
        dep_subst;
        destruct ec0;
        solve [inversion H; auto] 
    ] ].
  Qed.


  Lemma dec_term_val_empty : forall t k (v : value k), 
                                 dec_term t k = in_val v -> only_empty t k.
  Proof with auto.
    intros t k v H.
    destruct t;
    intros t0 k' c' H0 H1; generalize dependent t0;
    try solve
    [ induction c';
      intros t0 H0; simpl in *;
      [ intuition
      | destruct (IHc' (death_propagation2 _ _ H1) _ H0); dep_subst;
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
    destruct_all closure;
    try match goal with t0 : term0 |- _ => destruct t0 end;
    try solve [ inversion H; subst; inversion H0 ].
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


  Lemma elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

  Proof.
    intros t ec0 t' H k ec' H0.
    subst.

    destruct k, ec0, ec'; autof;
    unfold ec_order in H0; destruct H0 as (H, _);

    try solve
    [ exists (vECaCa v);
      simpl;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.

End no_es_cl_ECCa_Ref.




Require Import refocusing_semantics_derivation.
Require Import refocusing_machine.

Module no_es_cl_ECCa_REF_SEM := RedRefSem no_es_cl_ECCa_Ref.
Module ECCa_es_cl_EAM             := ProperEAMachine no_es_cl_ECCa no_es_cl_ECCa_REF_SEM.



Import ECCa_es_cl_EAM.
Import no_es_cl_ECCa_Ref.
Import no_es_cl_ECCa.


Fixpoint ec_in_context ec {k1 k2} (c : context k1 k2) :=
    match c with
    | [.]       => False
    | ec' =: c' => ec' = ec \/ ec_in_context ec c'
    end.

Fixpoint good_context {k1 k2} (c : context k1 k2) :=
    match c with
    | [.]                 => True
    | ap_r (Cl_t _) =: c' => good_context c'
    |        ap_r _ =: _  => False
    |             _ =: c' => good_context c'
    end.
    (*forall t, ec_in_context (ap_r t) c -> exists (cl : closure), t = cl.*)

Fixpoint good_term t k := 
    match t with
    | Cl_t _                => True
    | App (Cl_t _) (Cl_t _) => True
    | Var _                 => True
    | Lam t                 => C = k /\ good_term t C
    | OpVar _ _ _           => True
    | _                     => False
    end.

Definition good_value {k} (v : value k) :=
    match v with
    | vECaLam _ => False
    | _ => True
    end.

Definition good_state st :=
    match st with
    | c_eval t _ k c  => good_term t k /\ good_context c /\ k <> CBot
    | c_apply _ k c v => good_value v /\ good_context c /\ k <> CBot
    end.


Lemma sub_step_good : forall i j s e g k, good_term (sub_step i j s e g) k.
Proof.
  intros.
  unfold sub_step.
  destruct (lt_dec i j).
  - simpl; auto.
  - destruct s as [[t e'] | g'].
    + destruct (eq_nat_dec i j).
      * simpl; auto.
      * simpl; auto.
    + simpl; auto.
Qed.


Definition good_propagation1 : 
    forall (st1 st2 : configuration), good_state st1 -> st1 → st2 -> good_state st2.

Proof.
  intros st1 st2 H H0.
  destruct H0; try destruct H.
  
  - destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] ?] | ?], k2;
    try destruct tt1, tt2;
    inversion H; subst;
    try discriminate;
    inversion H0; subst. 
    + destruct l as [ | (?, ?) ?]; inversion H1. 
      * simpl; auto.
      * simpl; intuition.
        auto using sub_step_good.
    + destruct l as [ | (?, ?) ?]; inversion H1. 
      * simpl; auto.
      * simpl; intuition.
        auto using sub_step_good.
    + destruct l as [ | (?, ?) ?]; inversion H1.
      * simpl; auto.
      * simpl; auto.
    + inversion H1; simpl; auto.
    + inversion H1; simpl; auto.
    + destruct l as [ | (?, ?) ?]; inversion H1. 
      * simpl; auto.
      * simpl; intuition.
        auto using sub_step_good.
    + destruct l as [ | (?, ?) ?]; inversion H1. 
      * simpl; auto.
      * simpl; intuition.
        auto using sub_step_good.
  - destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] ?] | ?], k2;
    try destruct tt1, tt2;
    inversion H; subst;
    inversion H0; subst; 
    simpl; intuition.
  - destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] ?] | ?], k2;
    try destruct tt1, tt2;
    inversion H; subst;
    try discriminate;
    inversion H0; subst.
    + simpl in *; intuition.
    + simpl; intuition.
    + simpl; auto.
  - destruct ec0, k2; dependent destruction v; 
    inversion H0; subst; autof.
    + destruct t0; inversion H1; subst. simpl; intuition.
    + destruct t0; inversion H1; subst. simpl; intuition.
  - destruct ec0 as [ | tt | ? ], k2; destruct tt; simpl in H;
    dependent destruction v; 
    inversion H0; simpl in *; intuition. 
  - destruct ec0, k2; dependent destruction v;
    inversion H0; subst.
    + destruct t; simpl in *; intuition.
    + destruct t; simpl in *; intuition.
Defined.

Lemma good_propagation : 
    forall (st1 st2 : configuration), good_state st1 -> st1 →+ st2 -> good_state st2.

Proof.
  induction 2;
  eauto using good_propagation1.
Qed.

Definition progress : forall st, good_state st -> 
              (exists k v, st = c_apply [.](k) v) + { st' | st → st' }.
Proof.
  intros.
  destruct st.
  - right. 
    destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] [ | (?, ?) ?]] | ? [ | (?, ?) ?] ?], k2;
    try destruct tt1, tt2;

    destruct H as [? [? ?]];
    inversion H; autof;

    eexists; try solve [ apply t_val; simpl; intuition
                       | apply t_term; simpl; intuition
                       | eapply t_red; simpl; intuition].
  - destruct c.
    + left. dependent destruction v; eauto.
    + right. 
      destruct ec0 as [ | tt | ?], k2; dependent destruction v;
      destruct tt;
      destruct H as [? [? ?]]; try destruct H0; try destruct H;
      eexists; try solve [ apply t_cval; simpl; auto 
                         | eapply t_cred; [simpl; auto | simpl; auto] 
                         | apply t_cterm; simpl; auto].
Defined.


Require Import abstract_machine_facts.

Module Sim := DetAbstractMachine_Sim ECCa_es_cl_EAM.


Let tr := Lam0 (App0 (Lam0 (Lam0 (Var0 1))) (Var0 0)).

Eval compute in 
    Sim.n_steps 
    ( c_eval (Cl (Lam0 (App0  tr  (Var0 0))) ([]) : term)
             [.](C) )
    20.


Fixpoint nat_term0 n :=
    match n with
    | 0   => Lam0 (Lam0 (Var0 0))
    | S n => Lam0 (Lam0 (App0 (Var0 1) (App0 (App0 (nat_term0 n) (Var0 1)) (Var0 0))))
    end.


Let add_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0 
        (App0 (App0 (Var0 3) 
            (Var0 1)) 
            (App0 (App0 (Var0 2) (Var0 1)) (Var0 0)))))).

Let mul_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0
        (App0 (App0

        (App0 (App0 (Var0 2) 
            (Lam0 (App0 (App0 add_term0 (Var0 4)) (Var0 0)) ))
            (nat_term0 0))

        (Var0 1)) (Var0 0))))).


Eval compute in
    Sim.n_steps 
    ( c_eval (Cl (App0 (App0 mul_term0 (nat_term0 2)) (nat_term0 4)) ([]) : term) [.](C)) 
    536.
