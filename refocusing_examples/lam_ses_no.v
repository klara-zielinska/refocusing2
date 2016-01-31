Require Import Program
               Util
               refocusing_semantics.



(* Lambda calculus with simple explicit substitution for the normal-order strategy *)

Module Lam_SES_NO_PreRefSem <: PRE_PRECISE_REF_SEM.

  Require Export Peano_dec Compare_dec.


  Inductive term' :=
  | Var   : nat                   -> term'
  | Lam   : term'                 -> term'
  | App   : term' -> term'        -> term'
  | Sub   : term' -> nat -> term' -> term'
  | Shift : term' -> nat -> nat   -> term'.
  Definition term := term'.


  Inductive substitut := 
  | st_sub   : term -> substitut 
  | st_shift : nat -> substitut.
  Definition sub_tag := (nat * substitut) %type.


  Inductive ck := C | ECa | D | CBot.
  Definition ckind := ck.
  Hint Unfold ckind.


  Definition CECaD (k : ckind) := match k with CBot => False     | _ => True end.
  Definition CECa  (k : ckind) := match k with CBot | D => False | _ => True end.

  Hint Unfold CECaD CECa.

  Ltac destruct_all_CECaD :=
      repeat match goal with H : CECaD ?k |- _ => 
          try destruct k; destruct H
      end.
  Ltac destruct_all_CECa :=
      repeat match goal with H : CECa ?k |- _ => 
          try destruct k; destruct H
      end.


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
      | C    => match ec with lam_c => C    | ap_r _ => ECa | ap_l _ => C | 
                              stag_c _ => D end
      | ECa  => match ec with lam_c => CBot | ap_r _ => ECa | ap_l _ => C | 
                              stag_c _ => D end
      | D    => match ec with stag_c _ => D | _ => CBot end
      | CBot => CBot
      end.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).


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


  Lemma init_ckind_alive :
      ~dead_ckind init_ckind.

  Proof. auto. Qed.


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


  Lemma valCa_is_valECa : 
      forall v1 : valCa, exists v2 : value ECa, valCa_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vECaVar n)...
    - exists (vECaApp v1 v)...
  Qed.


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


  Instance dead_is_comp : CompPred _ dead_ckind.
      split. destruct x; auto. 
  Defined.


  Lemma death_propagation : 
      forall k ec, dead_ckind k -> dead_ckind (k+>ec).

  Proof.
    intros k ec H.
    destruct k;
    inversion H;
    solve [reflexivity].
  Qed.


  Lemma proper_death : forall k, dead_ckind k -> ~ exists (r : redex k), True.

  Proof with eauto.
    intros k H [r _].
    destruct r; inversion H; subst;
    solve [autof].
  Qed.


  Lemma value_trivial1 : forall {k} ec t,
      forall (v : value k), ~dead_ckind (k+>ec) -> ec:[t] = v ->
          exists (v' : value (k+>ec)), t = v'.

  Proof.
    intros k ec t v H H0.
    destruct ec, v; destruct_all sub_tag; destruct_all substitut; 
    inversion H0; subst;
    solve
    [ eautof
    | auto using valCa_is_valECa ].
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


  Lemma redex_trivial1 : forall {k} (r : redex k) ec t,
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.
  Proof.
    intros k r ec t H H0.
    destruct ec, r; destruct_all sub_tag; destruct_all substitut; destruct_all_CECaD;
    inversion H0; subst;
    try solve 
    [ eexists (vECaLam _); simpl; eauto
    | eexists (vCLam _); simpl; eauto
    | eexists (vDLam _); simpl; eauto
    | eexists (vECaApp _ _); simpl; eauto
    | eexists (vCApp _ _); simpl; eauto
    | eexists (vDApp _ _); simpl; eauto
    | eexists (vECaVar _); simpl; eauto
    | eexists (vCVar _); simpl; eauto
    | eexists (vDVar _); simpl; eauto
    | match goal with v: valCa |- _ => destruct v; discriminate end ].
  Qed.




  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].
  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof.
    REF_LANG_Help.prove_st_wf;

    solve (*rest with*)
    [ destruct_all sub_tag; destruct_all substitut;
      inversion H1; subst; 
      auto ].
  Qed.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order 
      := wf_clos_trans_l _ _ wf_immediate_subterm.

  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.
  Notation decomp'   := (@decomp ()).


  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.


  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End Lam_SES_NO_PreRefSem.




Module Lam_SES_NO_Strategy <: REF_STRATEGY Lam_SES_NO_PreRefSem.

  Import Lam_SES_NO_PreRefSem.


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




  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match k with
      | CBot | D => False
      | _        => match ec, ec0 with 
                    | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
                    | _, _           => False
                    end
      end.
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
               (at level 70, t, ec1, ec2 at level 50, no associativity).


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. REF_LANG_Help.prove_ec_wf. Qed.


  Lemma search_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Proof.
    intros k t ec ec0 H.
    destruct k, ec, ec0;
    solve [ autof ].
  Qed.


  Lemma search_order_trans :  forall k t ec0 ec1 ec2, 
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 -> 
      k,t |~ ec0 << ec2.

  Proof.
    intros k t ec0 ec1 ec2 H H0.
    destruct k, ec0, ec1;
    solve [ autof ].
  Qed.


  Lemma search_order_comp_if : forall t ec0 ec1 k, 
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k,t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ec0 = ec1.

  Proof.
    intros t ec0 ec1 k H0 H1 H2 H3.

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


  Lemma search_order_comp_fi :
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
      unfold search_order in G; destruct G as (G, _);
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
    unfold search_order in H0; destruct H0 as (H, _);
    destruct (valCa_is_valECa v) as (v0, H0);

    solve
    [ exists v0;
      simpl; rewrite <- H0;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.

End Lam_SES_NO_Strategy.





(* Contexts from the Johan Munk's paper *)

Module Lam_SES_NO_AlterContexts.

  Import Lam_SES_NO_PreRefSem.

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

End Lam_SES_NO_AlterContexts.




Module Lam_SES_NO_RefSem := PreciseRedRefSem Lam_SES_NO_PreRefSem Lam_SES_NO_Strategy.




Require Import refocusing_machine.

Module Lam_SES_NO_EAM := RefEvalApplyMachine Lam_SES_NO_RefSem.
