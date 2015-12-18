
Module Type RED_STRATEGY_LANG.

  Parameters term : Set.


  Parameter elem_context : Set.
  Parameter ckind        : Set. 
  Parameter ckind_trans : ckind -> elem_context -> ckind.
  Infix "+>" := ckind_trans (at level 50, left associativity).
  Parameter  init_ckind : ckind.
  Parameter  dead_ckind : ckind -> Prop.

  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).

  Parameter elem_plug : term -> elem_context -> term.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).

  Axiom elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.


  Definition immediate_ec ec t := exists t', ec:[t'] = t.


  Parameters value redex : ckind -> Set.

  Parameter value_to_term : forall {k}, value k -> term.
  Coercion  value_to_term : value >-> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Coercion  redex_to_term : redex >-> term.

  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Axiom proper_death : 
      forall k, dead_ckind k -> ~ exists (r : redex k), True.



  Axiom value_trivial1 : forall {k} (v : value k) ec {t}, 
                             ~dead_ckind (k+>ec) -> ec:[t] = v -> 
                                 exists (v' : value (k+>ec)), t = v'.
  Axiom value_redex    : forall {k} (v : value k) (r : redex k), 
                             value_to_term v <> redex_to_term r.


  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.


  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red _ r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.


End RED_STRATEGY_LANG.




Module Type RED_STRATEGY_STEP (R : RED_STRATEGY_LANG).

  Import R.


  (* interm_dec k - result of functions performing one step of decomposition of 
                    a term t from the symbol k to a redex.
     in_red r      - t is a redex, t = r.
     in_term t' ec - t = ec[t'] and to find a redex we are going to check t'.
     in_val v      - there is no redexes in t, t = v.
     in_dead       - result of the functions for arguments out of their domains. *)
  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_dead : interm_dec k.
  Arguments in_red {k} _.    Arguments in_val {k} _.
  Arguments in_term {k} _ _. Arguments in_dead {k}.


  (* dec_term t k       - one step of decomposition of t from the symbol k if we
                          have no information about subterms of t. 
                          Domain:  term * { k : ckind | k is not dead }  
     dec_context ec k v - one step of decomposition of a term ec[t] with an additional
                          piece of information saying that t is a value v. 
                          Domain:  elem_context * { (k, v) | k+>ec is not dead and
                                                             v : value (k+>ec)     }  *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.


  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r      => t = r
      | in_val v      => t = v
      | in_term t' ec => t = ec:[t']
      | in_dead       => dead_ckind k
      end.

  Axiom dec_term_from_dead : forall t k, 
      dead_ckind k -> dec_term t k = in_dead.


  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v'     => ec:[v] = v'
      | in_term t ec' => ec:[v] = ec':[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.


  Axiom dec_context_from_dead : forall ec k (v : value (k+>ec)), 
      dead_ckind (k+>ec) -> dec_context ec k v = in_dead.


  (* Any decomposition build by applying dec_term and dec_context needs to be proper. *)
  Axiom dec_term_next_alive : forall t k {t0 ec0}, 
      dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

  Axiom dec_context_next_alive : forall ec k v {t0 ec0}, 
      dec_context ec k v = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

End RED_STRATEGY_STEP.




Module Type RED_STRATEGY (R : RED_STRATEGY_LANG).

  Import R.

  Include RED_STRATEGY_STEP R.


  Parameter search_order : ckind -> term -> elem_context -> elem_context -> Prop.
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
               (at level 70, t, ec1, ec2 at level 50, no associativity).


(*  Axiom dec_term_red_atom : 
      forall t k {r : redex k}, dec_term t k = in_red r -> 
          ~exists ec, immediate_ec ec t /\ ~dead_ckind (k+>ec).

  Axiom dec_term_val_atom : 
      forall t k {v : value k}, dec_term t k = in_val v -> 
          ~exists ec, immediate_ec ec t /\ ~dead_ckind (k+>ec).*)

  Axiom dec_term_term_top : 
      forall t k {t' ec}, dec_term t k = in_term t' ec -> 
          forall ec',  ~ k, t |~ ec << ec'.


  Axiom dec_context_red_bot : 
      forall k ec v {r : redex k}, dec_context ec k v = in_red r -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_val_bot : 
      forall k ec v {v' : value k}, dec_context ec k v = in_val v' -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_term_next : 
      forall ec0 k v {t ec1}, dec_context ec0 k v = in_term t ec1 -> 
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.


  Axiom elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

End RED_STRATEGY.