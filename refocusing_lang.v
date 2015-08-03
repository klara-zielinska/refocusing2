Require Export Util.
Require Import Program.



(* Signature for languages with reduction semantics and multiple kinds of contextes. *)

Module Type RED_LANG.


  (* Note: (This describes only the simples use case.)
     The only grammar mentioned in this formalization is a grammar of contexts,
     thus any reference to a grammar means the grammar of contexts of the formalized
     language.

     In this formalisation we do not have a represenation for usual terminal 
     symbols in the grammar. Instead, we take whole right sides of productions that 
     contain non-terminals with non-terminals replaced by holes as terminals. Such 
     right sides are called elementary contexts.

     E.g., if k1, k2 are non-terminals and a, b, c are terminals, then the production 
     k1 -> a b k2 c  may be represented as  k1 -> (a b [] c) k2  , where  a b [] c  
     is an elementary context.

     Now, if we require all right sides that do not contain non-terminals to be 
     holes and existance of a production  k -> []  for any k, we can represent whole
     grammar only in terms of elementary contexts and non-terminals.

     We will call a hole generated from a symbol k >a hole of kind k< .

     Because each production has at most one non-terminal symbol this procedure 
     simplifies grammars of contexts to regular grammars on words. Let us call these 
     grammars >linearized grammars< .

     The requirement of productions  k -> []  does not break generality in our case,
     because we will later fix redexes that can occur in each kind of holes. So
     if we do not have a production  k -> []  in the original grammar, then we can 
     equvalently fix redexes for k as an empty set. *)



  (* Preconditions: To instaniate this module you need to linearize and determinize 
     the grammar of contextes of your language. If the result grammar is not total, 
     you need to include a sink non-terminal and totalize the grammar. *)



  Parameters term  elem_context : Set.
  Parameter  ckind : Set. (* kinds of contexts, that is, non-terminal symbols in 
                             the grammar *)


  Parameter  init_ckind : ckind. (* start symbol in the grammar *)
  Parameter  dead_ckind : ckind -> Prop. (* set of sink symbols *)


  (* ckind_trans - function that determinates the productions in the grammar, or 
                   in other words, a transition function of a finit automaton 
                   representing the grammar. *)
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Infix "+>" := ckind_trans (at level 50, left associativity).


  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).



  (* context k1 k2 - contexts of kind k1 (derivated from k1) with the hole of kind k2. 
                     Contexts are represented by reversed derivations from the grammar.
                     E.g., if a context is derivated by a sequence of productions
                     k1 -> ec1 k2, k2 -> ec2 k3, k3 -> ec3 k4, k4 -> [], then it is 
                     represented by the list  (ec3, k4)=:(ec2, k3)=:(ec1, k2)  and the
                     type of it is  context k1 k4  .
                     The second elements in the pairs are implicite. *)
  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.
  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

  (* Note: Contexts are reversed, because during evaluation by refocusing we always 
     access the elem. context nearest to the hole of a context. *)

  (* Definition: The hole of a context is >dead< if its kind is a sink symbol. *)
  (* Definition: A context is >proper< if its hole is not dead. 
     (Context with dead holes are contexts that cannot be generated in the orginal
     grammar.) *)



  (* Plugging is standard. You need to provide only plugging function for elem.
     contexts. *)

  Parameter elem_plug : term -> elem_context -> term.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0, t at level 99).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0, t at level 99).

  (* The following axiom somehow relates our representation of contexts to real
     contexts, but generally we can instantiate the module with elem. contexts
     that do not represent real elem. contexts. *)
  Axiom elem_plug_injective1 : forall ec {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.


  Definition immediate_ec ec t := exists t', ec:[t'] = t.



  (* redex k - representations of redexes that may occur in a hole of the kind k. 
     value k (where k is not a sink)
             - (almost) normal forms of kind k, that is, representations of terms
               that cannot be decomposed to a context k k' and a redex k'.  value k
               where k is a sink may be anything. *)
  Parameters value redex : ckind -> Set.


  Parameter value_to_term : forall {k}, value k -> term.
  Coercion  value_to_term : value >-> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Coercion  redex_to_term : redex >-> term.

  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.


  (* A key property of sink non-terminals: *)
  Axiom proper_death : forall k1, dead_ckind k1 -> 
                           ~ exists k2 (c : context k1 k2) (r : redex k2), True.


  (* Definition: A decomposition c[t] is empty if c is empty. *)
  (* Definition: A decomposition c[t] is proper if c is proper. *)

  (* only_empty t k   - the term t has only empty or improper decompositions from 
                        the non-terminal k.
     only_trivial t k - each proper decomposition of the term t from the symbol k is 
                        either empty or the component term is a value. *)
  Definition only_empty t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= @empty k.
  Definition only_trivial t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= @empty k \/ exists (v : value k'), t' = v.


  (* Axioms of normal forms: *)
  Axiom value_trivial : forall {k} (v : value k), only_trivial v k.
  Axiom value_redex   : forall {k} (v : value k) (r : redex k), 
                            value_to_term v <> redex_to_term r.
  Axiom trivial_val_red : 
      forall k t, only_trivial t k ->
         (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).



  (* Reduction of a redex (which may get stuck): *)
  Parameter contract : forall {k}, redex k -> option term.



  (* decomp k  - decomposition of a term t from the symbol k to a redex.
     d_red r c - t = c[r].
     d_val v   - t has no redexes and so it is a value, t = v. *)
  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red _ r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.



  (* Standard contexts composition: *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).

End RED_LANG.



Module Type DEC_STEP (R : RED_LANG).

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

  Axiom dec_term_from_dead : 
      forall t k, dead_ckind k -> dec_term t k = in_dead.

  Axiom dec_term_next_alive : 
      forall t k {t0 ec0}, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).


  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v'     => ec:[v] = v'
      | in_term t ec' => ec:[v] = ec':[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.

  Axiom dec_context_from_dead : 
      forall ec k (v : value (k+>ec)), dead_ckind (k+>ec) -> dec_context ec k v = in_dead.

  Axiom dec_context_next_alive : 
      forall ec k v {t0 ec0}, dec_context ec k v = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

End DEC_STEP.



Module Type RED_REF_LANG.

  Declare Module R   : RED_LANG.
  Declare Module DEC : DEC_STEP R.
  Export R.
  Export DEC.


  (* Additional requirement on redexes: *)
  Axiom redex_trivial : forall {k} (r : redex k), only_trivial r k.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall {t t0} ec, t = ec:[t0] -> subterm_one_step t0 t.
  Axiom wf_st1 : well_founded subterm_one_step.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Parameter ec_order : ckind -> term -> elem_context -> elem_context -> Prop.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).
  Axiom wf_eco : forall k t, well_founded (ec_order k t).

  Axiom ec_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Axiom ec_order_trans   : forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2.

  Axiom ec_order_comp_if : forall t ec0 ec1,
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1.

  Axiom ec_order_comp_fi : forall k t ec0 ec1,
      k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
                                  ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).


  Axiom dec_term_red_empty : 
      forall t k {r : redex k}, dec_term t k = in_red r -> only_empty t k.

  Axiom dec_term_val_empty : 
      forall t k {v : value k}, dec_term t k = in_val v -> only_empty t k.

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

End RED_REF_LANG.



Module RED_REF_LANG_Help.

  Ltac prove_st_wf := 
      intro t; constructor; induction t; 
      (
          intros ? H; 
          inversion H as [? ? ec DECT]; subst; 
          destruct ec; inversion DECT; subst; 
          constructor; auto
      ).

  Ltac prove_ec_wf := 
      intros k t ec; destruct k, t, ec; repeat 
      (
          constructor; 
          intros ec H; 
          destruct ec; inversion H; dep_subst; clear H
      ).

End RED_REF_LANG_Help.



Module Type ABSTRACT_MACHINE.

  Parameters term configuration value : Set.
  Parameter c_init  : term -> configuration.
  Parameter c_final : value -> configuration.
  Parameter transition : configuration -> configuration -> Prop.


  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), 
                     transition c0 c1 -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), 
                     transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.

End ABSTRACT_MACHINE.



(*Module Type SOS_SEM.

  Parameters term value : Set.
  Parameter step : term -> term -> Prop.
  Parameter value_to_term : value -> term.


  Inductive step_close : term -> value -> Prop :=
  | s_val  : forall v, step_close (value_to_term v) v
  | s_step : forall t t0 v, step t t0 -> step_close t0 v -> step_close t v.

End SOS_SEM.*)