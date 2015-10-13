Require Import Util.
Require Import Program.
Require Import refocusing_lang.
Require Import reduction_semantics_facts.


Module no_es_ECCaD <: RED_LANG.

  Require Export Peano_dec Compare_dec.


  Inductive __term :=
  | Var   : nat                     -> __term
  | Lam   : __term                  -> __term
  | App   : __term -> __term        -> __term
  | Sub   : __term -> nat -> __term -> __term
  | Shift : __term -> nat -> nat    -> __term.
  Definition term := __term.
  Hint Unfold term.


  Inductive substitut := 
  | st_sub   : term -> substitut 
  | st_shift : nat -> substitut.
  Definition sub_tag := (nat * substitut) %type.


  Inductive ck := C | ECa | D | CBot.
  Definition ckind := ck.
  Hint Unfold ckind.

  Definition CECaD (k : ckind) := match k with CBot => False     | _ => True end.
  Definition CECa  (k : ckind) := match k with CBot | D => False | _ => True end.


  Definition init_ckind : ckind     :=  C.
  Definition dead_ckind (k : ckind) :=  k = CBot.
  Hint Unfold init_ckind dead_ckind.


  Inductive val : ckind -> Type :=

  | vCLam   : val C -> val C
  | vCVar   : nat -> val C
  | vCApp   : valCa -> val C -> val C
  
  | vECaLam : term -> val ECa
  | vECaVar : nat -> val ECa
  | vECaApp : valCa -> val C -> val ECa

  | vDLam   : term -> val D
  | vDVar   : nat  -> val D
  | vDApp   : term -> term -> val D
  
  | vCBot   : term -> val CBot
  
  with valCa :=

  | vCaVar : nat -> valCa
  | vCaApp : valCa -> val C -> valCa.
  
  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val Sort Prop
    with valCa_Ind := Induction for valCa Sort Prop.


  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vCLam v => Lam (value_to_term v)
      | vCVar x => Var x
      | vCApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      | vECaLam t => Lam t
      | vECaVar x => Var x
      | vECaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      | vDLam t0 => Lam t0
      | vDVar n => Var n
      | vDApp t0 t1 => App t0 t1
      | vCBot t => t
      end

  with valCa_to_term v : term :=
      match v with
      | vCaVar x => Var x
      | vCaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valCa_to_term : valCa >-> term. 


  Definition vVar n k : value k := 
      match k with 
      | C => vCVar n | ECa => vECaVar n | D => vDVar n 
      | CBot => vCBot (Var n) 
      end.


  Inductive red : ckind -> Type :=
  | rCApp    : term -> term -> red C
  | rECaApp  : term -> term -> red ECa
  | rSubVar  : forall k, CECaD k -> nat          -> sub_tag -> red k
  | rSubLam  : forall k, CECaD k -> term         -> sub_tag -> red k
  | rSubApp  : forall k, CECaD k -> term -> term -> sub_tag -> red k.
  Definition redex := red.
  Hint Unfold redex.


  Inductive ec :=
  | lam_c  : ec
  | ap_r   : term -> ec
  | ap_l   : valCa -> ec
  | stag_c : sub_tag -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.


  Definition elem_plug (t : term) (ec : elem_context) : term :=
      match ec with
      | lam_c => Lam t
      | ap_r tr => App t tr
      | ap_l v  => App (v : term) t
      | stag_c (j, st_sub t') => Sub t j t'
      | stag_c (j, st_shift g) => Shift t j g
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Definition ckind_trans (k : ckind) (ec : elem_context) := 
      match k with
      | C    => match ec with lam_c => C    | ap_r _ => ECa | ap_l _ => C | stag_c _ => D end
      | ECa  => match ec with lam_c => CBot | ap_r _ => ECa | ap_l _ => C | stag_c _ => D end
      | D    => match ec with stag_c _ => D | _ => CBot end
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


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rCApp t1 t2   => App (Lam t1) t2
      | rECaApp t1 t2 => App (Lam t1) t2
      | rSubVar _ _ n d     => (stag_c d):[Var n]
      | rSubLam _ _ t d     => (stag_c d):[Lam t]
      | rSubApp _ _ t1 t2 d => (stag_c d):[App t1 t2]
      end.
  Coercion redex_to_term : redex >-> term.



  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

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
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct k;
    dependent destruction r; dependent destruction r'; 
    destruct_all sub_tag; destruct_all substitut; 
    inversion H; subst;

    solve
    [ repeat match goal with H : CECaD ?k |- _ => try destruct k; destruct H end;
      f_equal; auto ].
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
    destruct_all sub_tag; destruct_all substitut;
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


  Definition contract0 {k} (r : redex k) : term :=
      match r with
      | rCApp   t0 t1 => Sub t0 0 t1
      | rECaApp t0 t1 => Sub t0 0 t1
      | rSubVar _ _ i  (j, st_sub t)   => if lt_dec i j     then Var i else 
                                          if eq_nat_dec i j then Shift t 0 j
                                                            else Var (pred i)
      | rSubVar _ _ i  (j, st_shift g) => if lt_dec i j     then Var i
                                                            else Var (i+g)
      | rSubLam _ _ t  (j, d)          => Lam ((stag_c (S j, d)):[t])
      | rSubApp _ _ t1 t2 d            => App (stag_c d):[t1] (stag_c d):[t2]
      end.
  Definition contract {k} (r : redex k) := Some (contract0 r).


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
    - exists (vECaVar n)...
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
      destruct_all sub_tag; destruct_all substitut;

      solve
      [ eautof | apply valCa_is_valECa | destruct t0; discriminate ].
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v; 
    simpl;
    try match goal with 
    | |- App (valCa_to_term ?v) _ <> _ => dependent_destruction2 v
    end;
    destruct_all sub_tag; destruct_all substitut;
    
    solve [ discriminate | tauto ].
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
    intros k t; revert k.
    induction t;
        intros k H;
        destruct k.
    
    - left; eexists (vCVar _)...

    - left; eexists (vECaVar _)...

    - left; eexists (vDVar _)...

    - left; eexists (vCBot (Var _))...

    - destruct (ot_subterm_val _ t lam_c _ H)...
      subst.
      left; eexists (vCLam _); subst...

    - left; eexists (vECaLam _)...

    - left; eexists (vDLam _)...

    - left; eexists (vCBot (Lam _))...

    - destruct (ot_subterm_val _ t1 (ap_r t2) _ H) as (v, H0)...
      subst.
      simpl in v; dependent destruction v.
      + right; eexists (rCApp _ _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaVar n)) _ H) as (v0, H0)...
        subst.
        left; eexists (vCApp (vCaVar _) _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaApp v v1)) _ H) as (v0, H0)...
        subst.
        left; eexists (vCApp (vCaApp _ _) _)...

      (* almost "copy-past" of the previous case *)
    - destruct (ot_subterm_val _ t1 (ap_r t2) _ H) as (v, H0)...
      subst.
      simpl in v; dependent destruction v.
      + right; eexists (rECaApp _ _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaVar n)) _ H) as (v0, H0)...
        subst.
        left; eexists (vECaApp (vCaVar _) _)...
      + destruct (ot_subterm_val _ t2 (ap_l (vCaApp v v1)) _ H) as (v0, H0)...
        subst.
        left; eexists (vECaApp (vCaApp _ _) _)...

    - left; eexists (vDApp _ _)... 

    - left; eexists (vCBot (App _ _))...

    - destruct (ot_subterm_val _ t1 (stag_c (n, st_sub t2)) _ H)...
      right.
      dependent destruction x.
      + eexists (rSubLam C I _   (_, st_sub _)); subst; simpl...
      + eexists (rSubVar C I _   (_, st_sub _)); subst; simpl...
      + eexists (rSubApp C I _ _ (_, st_sub _)); subst; simpl...

    - destruct (ot_subterm_val _ t1 (stag_c (n, st_sub t2)) _ H)...
      right.
      dependent destruction x.
      + eexists (rSubLam ECa I _   (_, st_sub _)); subst; simpl...
      + eexists (rSubVar ECa I _   (_, st_sub _)); subst; simpl...
      + eexists (rSubApp ECa I _ _ (_, st_sub _)); subst; simpl...

    - destruct (ot_subterm_val _ t1 (stag_c (n, st_sub t2)) _ H)...
      right.
      dependent destruction x.
      + eexists (rSubLam D I _   (_, st_sub _)); subst; simpl...
      + eexists (rSubVar D I _   (_, st_sub _)); subst; simpl...
      + eexists (rSubApp D I _ _ (_, st_sub _)); subst; simpl...

    - left; eexists (vCBot (Sub _ _ _))...

    - destruct (ot_subterm_val _ t (stag_c (n, st_shift n0)) _ H)...
      right.
      dependent destruction x.
      + eexists (rSubLam C I _   (_, st_shift _)); subst; simpl...
      + eexists (rSubVar C I _   (_, st_shift _)); subst; simpl...
      + eexists (rSubApp C I _ _ (_, st_shift _)); subst; simpl...

    - destruct (ot_subterm_val _ t (stag_c (n, st_shift n0)) _ H)...
      right.
      dependent destruction x.
      + eexists (rSubLam ECa I _   (_, st_shift _)); subst; simpl...
      + eexists (rSubVar ECa I _   (_, st_shift _)); subst; simpl...
      + eexists (rSubApp ECa I _ _ (_, st_shift _)); subst; simpl...

    - destruct (ot_subterm_val _ t (stag_c (n, st_shift n0)) _ H)...
      right.
      dependent destruction x.
      + eexists (rSubLam D I _   (_, st_shift _)); subst; simpl...
      + eexists (rSubVar D I _   (_, st_shift _)); subst; simpl...
      + eexists (rSubApp D I _ _ (_, st_shift _)); subst; simpl...

    - left; eexists (vCBot (Shift _ _ _))...
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
           | H : CECaD ?k |- _ => try destruct k; destruct H
           end;
           solve [discriminate H0].
  Qed.



  (* Contexts from the Johan Munk's paper *)
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

    induction c as  [ | ec k2 c IHc].
    
    (* c = [.] *)
    - destruct k1.
      + exact hole_io.
      + exact (a_is_c_io hole_io).
      + exact (a_is_d_io hole_io).
      + exact ().
    
    (* c = (ec=:c') *)
    - set (e:=ec).
      destruct k2, ec; simpl;
      match goal with
      | e := lam_c                           |- _ => exact (lam_c_io IHc)
      | e := ap_r ?t, IHc : context_IO Aio   |- _ => exact (ap_r_io (a_is_c_io IHc) t)
      | e := ap_r ?t, IHc : context_IO Cio   |- _ => exact (ap_r_io IHc t)
      | e := ap_l ?v, IHc : context_IO Aio   |- _ => exact (ap_l_io (a_is_c_io IHc) v)
      | e := ap_l ?v, IHc : context_IO Cio   |- _ => exact (ap_l_io IHc v)
      | e := stag_c ?d, IHc : context_IO Aio |- _ => exact (stag_c_io (a_is_d_io IHc) d)
      | e := stag_c ?d, IHc : context_IO Cio |- _ => exact (stag_c_io (c_is_d_io IHc) d)
      | e := stag_c ?d, IHc : context_IO Dio |- _ => exact (stag_c_io IHc d)
      | _                                         => exact ()
      end.
  Defined.


  Definition context_from_IO {k} (c : context_IO k) : 
               match k with  
               | Aio => context C C | Cio => context C C + context C ECa 
               | Dio => context C C + context C ECa + context C D
               end.

    set (c0:=c).
    induction c as [ | ? IHc ? | ? IHc | ? IHc | ? IHc ? | ? IHc | ? IHc ?]; simpl in *;
    match goal with
    | c0 := hole_io        |- _ => exact [.]
    | c0 := ap_l_io _ ?v   |- _ => destruct IHc as [IHc | IHc];
                                   exact (ap_l v=:IHc)
    | c0 := lam_c_io _     |- _ => exact (lam_c=:IHc)
    | c0 := a_is_c_io _    |- _ => exact (inl IHc)
    | c0 := ap_r_io _ ?t   |- _ => destruct IHc as [IHc | IHc];
                                   exact (inr (ap_r t=:IHc))
    | c0 := c_is_d_io _    |- _ => exact (inl IHc)
    | c0 := stag_c_io _ ?d |- _ => destruct IHc as [[IHc | IHc] | IHc];
                                   exact (inr (stag_c d=:IHc))
    end.
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
    induction c; 
        simpl;
        repeat match goal with
        | _ : context [match ?s with inl _ => _ | inr _ => _ end] |- _ => destruct s
        end;
        try subst;
    solve
    [ simpl; f_equal; auto ].
  Qed.


  Lemma from_to_IO_is_id : 
            forall k (c : context C k),
                match k as k return context C k -> Prop with
                | C    => fun c =>     c = context_from_IO (context_to_IO c)
                | ECa  => fun c => inr c = context_from_IO (context_to_IO c)
                | D    => fun c => inr c = context_from_IO (context_to_IO c)
                | CBot => fun c => True
                end c.
  Proof.
    induction c as [ | ec k2 ? IHc].
    - simpl; auto.
    - destruct k2, ec; 
      simpl; 
      try rewrite <- IHc; 
      solve [congruence | auto].
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
    - destruct k1; auto.
    - destruct k2, ec0; 
      destruct_all sub_tag; destruct_all substitut; 
      solve [simpl in *; auto].
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
    intros k c t.
    symmetry.
    destruct k;
        first
        [ rewrite (to_from_IO_is_id Aio) at 2
        | rewrite (to_from_IO_is_id Cio) at 2
        | rewrite (to_from_IO_is_id Dio) at 2 ];
        repeat match goal with
        | |- context [match ?s with inl _ => _ | inr _ => _ end] => destruct s
        end;
    solve
    [ apply @plug_compatible with (k2 := C)
    | apply @plug_compatible with (k2 := ECa)
    | apply @plug_compatible with (k2 := D) ].
  Qed.

End no_es_ECCaD.




Module no_es_ECCaD_Ref <: RED_REF_LANG.

  Module R  := no_es_ECCaD.
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
                  | App t1 t2 => in_term t1 (ap_r t2)
                  | Var n     => in_val (vCVar n)
                  | Lam t1    => in_term t1 lam_c
                  | Sub t1 n t2   => in_term t1 (stag_c (n, st_sub t2))
                  | Shift t1 n t2 => in_term t1 (stag_c (n, st_shift t2))
                  end
        | ECa  => match t with
                  | App t1 t2 => in_term t1 (ap_r t2)
                  | Var n     => in_val (vECaVar n)
                  | Lam t1    => in_val (vECaLam t1)
                  | Sub t1 n t2   => in_term t1 (stag_c (n, st_sub t2))
                  | Shift t1 n t2 => in_term t1 (stag_c (n, st_shift t2))
                  end
        | D    => match t with
                  | App t1 t2 => in_val (vDApp t1 t2)
                  | Var n     => in_val (vDVar n)
                  | Lam t1    => in_val (vDLam t1)
                  | Sub t1 n t2   => in_term t1 (stag_c (n, st_sub t2))
                  | Shift t1 n t2 => in_term t1 (stag_c (n, st_shift t2))
                  end
        | CBot => in_dead
        end.


    Definition dec_context ec k (v : value (k+>ec)) : interm_dec k :=

        match ec as ec0 return value (k+>ec0) -> interm_dec k with

        | lam_c    => match k as k0 return value (k0+>lam_c) -> interm_dec k0 with
                      | C    => fun v => in_val (vCLam v)
                      | ECa  => fun _ => in_dead
                      | D    => fun _ => in_dead
                      | CBot => fun _ => in_dead
                      end

        | ap_r t   => match k as k0 return value (k0+>(ap_r t)) -> interm_dec k0 with
                      | C    => fun v => 
                                    match v with
                                    | vECaLam t0    => in_red (rCApp t0 t)
                                    | vECaVar n     => in_term t (ap_l (vCaVar n))
                                    | vECaApp v1 v2 => in_term t (ap_l (vCaApp v1 v2))
                                    | _ => @in_dead C
                                    end
                      | ECa  => fun v => 
                                    match v with
                                    | vECaLam t0    => in_red (rECaApp t0 t)
                                    | vECaVar n     => in_term t (ap_l (vCaVar n))
                                    | vECaApp v1 v2 => in_term t (ap_l (vCaApp v1 v2))
                                    | _ => @in_dead ECa
                                    end
                      | D    => fun _ => in_dead
                      | CBot => fun _ => in_dead
                      end

        | ap_l v0  => match k as k0 return value (k0+>(ap_l v0)) -> interm_dec k0 with
                      | C    => fun v => in_val (vCApp v0 v)
                      | ECa  => fun v => in_val (vECaApp v0 v)
                      | D    => fun _ => in_dead
                      | CBot => fun _ => in_dead
                      end

        | stag_c d => match k as k0 return value (k0+>(stag_c d)) -> interm_dec k0 with
                      | CBot => fun _ => in_dead
                      | k0   => fun v => 
                                    match v with
                                    | vDLam t0    => in_red (rSubLam k0 I t0 d)
                                    | vDVar n     => in_red (rSubVar k0 I n  d)
                                    | vDApp t1 t2 => in_red (rSubApp k0 I t1 t2 d)
                                    | _ => @in_dead k0
                                    end
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
      intros t k H.
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
            destruct ec0; destruct vr; destruct_all sub_tag; destruct_all substitut;
            dependent_destruction2 Hvr
      end;
      try match goal with
      | H : CECaD ?k |- _ => destruct k; simpl in H
      end;

      solve 
      [ eautof 
      | apply valCa_is_valECa
      | eexists (vECaLam _); simpl; auto 
      | dependent destruction v; discriminate
      | eexists (vDVar _); simpl; auto
      | eexists (vDLam _); simpl; auto
      | eexists (vDApp _ _); simpl; auto ].
  Qed.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec, t = ec:[t0] -> subterm_one_step t0 t.


  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    RED_REF_LANG_Help.prove_st_wf;

    destruct_all sub_tag; destruct_all substitut;
    inversion H1; dep_subst; 
    auto.
  Qed.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Definition ec_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match k with
      | CBot | D => False
      | _        => match ec, ec0 with 
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
    destruct_all sub_tag; destruct_all substitut;
    inversion H5; subst;

    solve
    [ compute; eautof 7
    | do 2 right; 
      f_equal;
      apply valCa_to_term_injective; auto ].
  Qed.


  Lemma ec_order_comp_fi :
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
          ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

  Proof with auto.
    intros k t ec0 ec1 H.
    destruct k, ec0, ec1;
    destruct_all sub_tag; destruct_all substitut;
    inversion H;
    solve [auto].
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
        destruct_all sub_tag; destruct_all substitut;
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
    destruct (valCa_is_valECa v) as (v0, H0);

    solve
    [ exists v0;
      simpl; rewrite <- H0;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.

End no_es_ECCaD_Ref.




Require Import refocusing_semantics_derivation.
Require Import refocusing_machine.

Module no_es_ECCaD_REF_SEM := RedRefSem no_es_ECCaD_Ref.
Module ECCaD_EAM           := ProperEAMachine no_es_ECCaD no_es_ECCaD_REF_SEM.