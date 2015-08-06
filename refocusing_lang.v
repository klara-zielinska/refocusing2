Require Export Util.
Require Import Program.


(* Note: The only grammar mentioned in this formalization is a grammar of evaluation
   contexts, thus any reference to a grammar means the grammar of contexts of 
   the formalized language.
   
   In this formalisation we represent evaluation contexts in terms of elementary
   contexts (if you do not understand this go to the paper). To find the elem.
   contexts and the grammar of eval. contexts given in terms of elem. contexts, first 
   translate the original grammar to a form where each right side of a production is 
   a hole or it has a context non-terminal, then take each non-hole right side and 
   replace the context symbol by a hole. The result is a context pattern - we will
   use EC markings for them.

   E.g., if k1, k2 are context symbols and there is a production  k1 -> a b k2 c  ,
   then the result context pattern is  a b [] c  .

   Contexts that match the patterns are elem. contexts. However, not every grmmar is
   proper for our formalisation, so you may still need to refine it both with the set 
   of elem. contexts.

   First of all, for any context symbol k and elem. context ec there needs to at most
   one k' such that there exists a production  k -> EC[k']  and ec matches EC. Let us
   call such grammar a >deterministic grammar of contexts<. 

   You may achive this form by spliting the context patterns and determinizing 
   the grammar. E.g., suppose you have a grammar with two productions form k1:  
   k1 -> a k2 a,  k1 -> ab k3 ab,  where L(ab) = L(a) U L(b) and languages L(a), L(b) 
   are disjoint. Then you may split the second pattern  ab [] ab  to:  a [] a,  b [] ab,  
   ab [] b. So now, the second production is replaced by three: k1 -> a k3 a,  
   k -> b k3 ab,  k -> ab k3 b. Then, you may determinize the grammar. This will cause 
   an introduction of a new context symbol {k2,k3}, replacing the two productions:  
   k1 -> a k2 a,  k1 -> a k3 a,  with  k1 -> a {k2,k3} a  and derivating the missing 
   part of the grammar from the symbol {k2,k3}. 

   Second of all, the production  k -> []  must be present in the grammar for any k.
   You may just add the missing ones. This does not break any generality in our case,
   because in our formalisation you may define a set of redexes per each kind of
   a hole. So, if there was no production  k -> [],  then you may just set up 
   an empty set of redexes for k.

   Definition: If a derivation of a context ends with a production k -> [], then
   we say that the context has a >hole of the kind k<. *)



(* Signature for languages with reduction semantics and multiple kinds of contextes. *)

Module Type RED_LANG.

  (* Preconditions: To instaniate this module you need to determinizethe grammar of 
     contextes. *)


  Parameters term  elem_context : Set.
  Parameter  ckind : Set. (* kinds of contexts, that is, non-terminal context symbols 
                             in the grammar *)


  Parameter  init_ckind : ckind.         (* start symbol in the grammar *)
  Parameter  dead_ckind : ckind -> Prop. (* set of sink symbols; if your grammar
                                            is not total you need to introduce at least
                                            one *)


  (* ckind_trans - function that determinates the productions in the grammar, that is,
                   if ckind_trans k1 ec = k2, then k1 -> EC[k2] where ec matches EC or
                   there is no such production and k2 is a sink. 
                   In other words, it is the transition function of a finit automaton 
                   representing the totalized grammar. *)
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Infix "+>" := ckind_trans (at level 50, left associativity).


  (* The sink property: *)
  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).



  (* context k1 k2 - contexts of kind k1 (derivated from k1) with a hole of kind k2. 
                     Contexts are represented by reversed derivations in the grammar.
                     E.g., if a context is derivated by a sequence of productions
                     k1 -> ec1 k2, k2 -> ec2 k3, k3 -> ec3 k4, k4 -> [], then it is 
                     represented by the list  (ec3, k4), (ec2, k3), (ec1, k2)  ot 
                     the type  context k1 k4.
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

  (* The following axiom, somehow, relates our representation of contexts to the 
     real eval. contexts, but generally we can instantiate the module with 
     elem. contexts that do not represent real elem. contexts and so not
     every module of this signature is a proper. *)
  Axiom elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.


  (* An intuitive definition: *)
  Definition immediate_ec ec t := exists t', ec:[t'] = t.



  (* redex k - representations of redexes that may occur in a hole of the kind k. 
     value k where k is not a sink
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
                        the symbol k.
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


  (* A property of deterministic reduction semantics: *)
  Axiom redex_trivial : forall {k} (r : redex k), only_trivial r k.



  (* Reduction of a redex (it may get stuck): *)
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


  (* Any decomposition build by applying dec_term and dec_context needs to be 
     proper. *)
  Axiom dec_term_next_alive : forall t k {t0 ec0}, 
      dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

  Axiom dec_context_next_alive : forall ec k v {t0 ec0}, 
      dec_context ec k v = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

End DEC_STEP.



Module Type RED_REF_LANG.

  Declare Module R   : RED_LANG.
  Declare Module DEC : DEC_STEP R.
  Export R.
  Export DEC.


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