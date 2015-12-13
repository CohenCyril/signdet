From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
From mathcomp Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint rat tuple.
From mathcomp Require Import interval matrix mxalgebra binomial.
From mathcomp Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope ring_scope.
Local Open Scope nat_scope.
(* Local Open Scope ring_scope. *)

Section extrassr.

Lemma fintype1 (T : finType) (x : T) : #|T| = 1 -> all_equal_to x.
Proof.
move=> /eqP T1 y /=; apply: contraTeq T1 => neq_yx.
suff: #|T| >= #|[set y; x]| by rewrite cards2 neq_yx => /gtn_eqF ->.
by apply/subset_leqif_card/subsetP=> z /set2P [] ->; rewrite inE.
Qed.

Definition ffun0 (T : finType) (X : Type) : #|T| = 0 -> {ffun T -> X}.
Proof. by move=> /card0_eq T0; apply: finfun => t; move: (T0 t). Defined.

Lemma bump_small n i : i < n -> bump n i = i.
Proof. by move=> ltin; rewrite /bump leqNgt ltin add0n. Qed.

Lemma lift_ord_max n (i : 'I_n) :
   lift ord_max i = widen_ord (leqnSn n) i.
Proof. by apply: val_inj=> /=; rewrite bump_small. Qed.

Lemma insubd_id (X : Type) (P : pred X) (S : subType P) (x y : S) :
  insubd x (val y) = y.
Proof. by apply: val_inj; rewrite insubdK //; apply: valP. Qed.

Lemma leqif_eq n m C : n <= m ?= iff C -> C -> n = m.
Proof. by case: C => [[_ /eqP]|//]. Qed.

End extrassr.

Section Ext.

(* Extension of s with one element x at the end *)
Definition extelt n (X : finType) (x : X) (s : X ^ n) : X ^ n.+1 :=
  [ffun i => if unlift ord_max i is Some j then s j else x].

(* Restriction of b, without the last element, the inverse of extelt *)
Definition restrict n (X : finType) (b : X ^ n.+1) : X ^ n :=
  [ffun i => b (lift ord_max i)].

(* extension of a set with one element x at the end. *)
Definition extset n (X : finType) (x : X) (S : {set X ^ n}) :
   {set X ^ n.+1} :=  [set extelt x s | s in S].

(* the set of possible extensions of s in S *)
Definition exts (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) : {set X} :=
  [set x | extelt x s \in S].

Program Definition tupleext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :=
  @Tuple k _ (sort (fun i j => val i <= val j) (enum (exts S s))
                   ++ enum (~: exts S s)) _.
Next Obligation.
rewrite size_cat ?size_sort -!cardE -cardsUI addnC.
set A := _ :|: _; set B := _ :&: _.
suff [-> ->] : (A = setT) /\ (B = set0) by rewrite cardsT card_ord cards0.
by split; apply/setP => i; rewrite !inE ?andbN ?orbN.
Qed.

Lemma tupleext_uniq k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
  uniq (tupleext S s).
Proof.
rewrite cat_uniq ?sort_uniq ?enum_uniq andbT; apply/hasPn=> x.
by rewrite /= mem_sort !mem_enum !inE.
Qed.

Lemma mem_tupleext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) x :
  x \in tupleext S s.
Proof. by rewrite mem_cat mem_sort !mem_enum !inE orbN. Qed.

(* The nth, last element of the extension of s in S *)
Definition nthext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) (m : 'I_k) :
  'I_k := tnth (tupleext S s) m.

(* the inverse of nthext *)
Program Definition indexext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n)
  (i : 'I_k) := @Ordinal k (index i (tupleext S s)) _.
Next Obligation.
by have := index_mem i (tupleext S s); rewrite mem_tupleext size_tuple.
Qed.

(* the set of elements with at least m extensions in S,
  Xi 1 is the inverse of restrict *)
(* Definition Xi n (X : finType) (m : nat) (S : {set X ^ n.+1}) : {set X ^ n}:= *)
(*   [set s : X ^ n | [exists (E : {set X} | #|E| == m),  *)
(*                     forall x in E, extelt x s \in S]]. *)
Definition Xi n (X : finType) (m : nat) (S : {set X ^ n.+1}) : {set X ^ n}:=
  [set s : X ^ n | m <= #|exts S s|].

(* The nth extension in S *)
Definition reext k n (S : {set 'I_k ^ n.+1}) (m : 'I_k) :
  {set 'I_k ^ n.+1} :=
  [set extelt (nthext S s m) s | s in Xi m.+1 S].

Lemma restrictK n (X : finType) (b : X ^ n.+1) :
  extelt (b ord_max) (restrict b) = b.
Proof.
by apply/ffunP=> i; rewrite ffunE; case: unliftP => [j|] ->; rewrite ?ffunE.
Qed.

Lemma exteltK n (X : finType) (x : X) : cancel (extelt x) (@restrict n _).
Proof. by move=> b ;apply/ffunP=> i; rewrite !ffunE liftK. Qed.

Lemma restrictP n (X : finType) (S : {set X ^ n.+1})
      (x : X ^ n.+1) (y : X ^ n) :
  reflect (exists i, x = extelt i y) (restrict x == y).
Proof.
apply: (iffP eqP) => [<-|[i ->]]; last by rewrite exteltK.
by exists (x ord_max); rewrite restrictK.
Qed.

Lemma extelt_ord_max  n (X : finType) (x : X) (s : X ^ n) :
  (extelt x s) ord_max = x.
Proof. by rewrite /extelt ffunE unlift_none. Qed.

Lemma extelt_small (X : finType) (x : X) n (i : 'I_n.+1)
  (b : X ^ n) (lt_in : i < n) : (extelt x b) i = b (Ordinal lt_in).
Proof.
rewrite ffunE; case: unliftP=> [j|] i_def; last first.
  by suff: false by []; rewrite i_def ltnn in lt_in *.
by congr (b _); apply: val_inj; rewrite /= i_def /= bump_small.
Qed.

Definition extE1 := (inE, extelt_ord_max, exteltK, restrictK, eqxx).

Lemma eq_extelt n (X : finType) (x x' : X) (s s' : X ^ n) :
  (extelt x s == extelt x' s') = (x == x') && (s == s').
Proof.
have [->|] /= := altP (x =P x'); first by rewrite (can_eq (exteltK _)).
apply: contraNF => /eqP /(congr1 (fun u : _ ^ _ => u ord_max)).
by rewrite !extelt_ord_max => ->.
Qed.

Lemma exts0 n (X : finType) (s : X ^ n) : exts set0 s = set0.
Proof. by apply/setP=> i; rewrite !inE. Qed.

Lemma card_exts (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) :
  #|exts S s| <= #|X|.
Proof. by rewrite subset_leq_card //; apply/subsetP. Qed.

Lemma extelt_in (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) x :
 (extelt x s \in S) = (x \in exts S s).
Proof. by rewrite inE. Qed.

Lemma nthextK k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
  cancel (nthext S s) (indexext S s).
Proof.
move=> i; apply/val_inj; rewrite /= /indexext index_uniq ?tupleext_uniq //.
by rewrite size_tuple ltn_ord.
Qed.

Lemma indexextK k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
  cancel (indexext S s) (nthext S s).
Proof. by move=> x; rewrite /nthext /tnth nth_index // mem_tupleext. Qed.

Lemma nthext_in k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) (i : 'I_k) :
  (nthext S s i \in exts S s) = (i < #|exts S s|).
Proof.
rewrite /nthext /tnth nth_cat size_sort -!cardE.
have [i_small|i_big] //= := ltnP i _.
  rewrite -mem_enum -(mem_sort (fun i j => val i <= val j)).
  by rewrite mem_nth ?size_sort -?cardE.
apply: negbTE; rewrite -in_setC -mem_enum mem_nth // -?cardE.
by rewrite -subSn // leq_subLR cardsC card_ord.
Qed.

Lemma ord_ext_subproof k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) (i : 'I_k) :
  (i < #|exts S s|) -> i < k.
Proof. by move=> /leq_trans /(_ (card_exts _ _)); rewrite card_ord. Qed.

Definition ord_ext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) (i : 'I_k)
  (i_small : i < #|exts S s|) := Ordinal (ord_ext_subproof i_small).

Lemma in_exts k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) x :
  (x \in exts S s) = (indexext S s x < #|exts S s|).
Proof. by rewrite -nthext_in indexextK. Qed.

Lemma nthext_inj k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
  injective (nthext S s).
Proof. exact: can_inj (@nthextK _ _ _ _). Qed.

Lemma subset_exts (X : finType) n (s : X ^ n) :
  {homo (fun S => exts S s) : S S' / S \subset S'}.
Proof.
by move=> S S' /subsetP SsubS'; apply/subsetP => x; rewrite !inE => /SsubS'.
Qed.

Lemma leq_index (T : eqType) (x : T) s s' : x \in s ->
  uniq s' -> subseq s s' -> index x s <= index x s'.
Proof.
move=> xs' us' /subseqP [m sm s_eq]; rewrite s_eq in xs' * => {s s_eq}.
elim: s' m sm us' xs' => [//|y r IHr] [|[] m] //= [sm] /andP [/negPf ys' us'].
   by rewrite inE eq_sym; have [//|? /IHr] := altP eqP; apply.
by have [<- /mem_mask|? xs'] := altP eqP; [rewrite ys'|apply/leqW/IHr].
Qed.

Lemma sub_indexext k n (S S' : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) x :
  x \in exts S s -> S \subset S' -> indexext S s x <= indexext S' s x.
Proof.
move=> sS SsubS'; rewrite /indexext /= !index_cat ?mem_sort ?mem_enum sS.
rewrite (subsetP (subset_exts _ SsubS')) //.
rewrite leq_index ?mem_sort ?mem_enum ?sort_uniq ?enum_uniq //.
set l1 := sort _ _; set l2 := sort _ _.
suff -> : l1 = [seq y <- l2 | y \in exts S s] by apply: filter_subseq.
apply: (@eq_sorted _ (fun (i j : 'I_k) => val i <= val j)).
- exact: leq_trans.
- by move=> a b ?; apply/val_inj/anti_leq.
- exact/sort_sorted/leq_total.
- by rewrite sorted_filter; [|apply: leq_trans|apply/sort_sorted/leq_total].
rewrite uniq_perm_eq // ?filter_uniq ?sort_uniq ?enum_uniq // => i.
rewrite mem_filter ?mem_sort ?mem_enum; symmetry.
by have [|] //= := boolP (i \in exts S s); apply/subsetP/subset_exts.
Qed.

(* Lemma leq_nthext_in k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) x y : *)
(*   indexext S s y <= indexext S s x -> x \in exts S s -> y \in exts S s. *)
(* Proof. *)
(* move=> leq_yx. *)
(* rewrite !inE. *)


  (* x \in exts S s -> S \subset S' -> indexext S s x <= indexext S' s x. *)



Lemma leq_exts (X : finType) n m (S : {set X ^ n.+1}) (s : X ^ n) :
  (m <= #|exts S s|) = (s \in Xi m S).
Proof. by rewrite inE. Qed.

Lemma exts_leq k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
 #|exts S s| <= k.
Proof. by rewrite (leq_trans (card_exts _ _)) ?card_ord. Qed.
Hint Resolve exts_leq.

Lemma exts_restrict_neq0 (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> exts S (restrict s) != set0.
Proof.
move=> sS; have : s ord_max \in exts S (restrict s).
  by rewrite inE ?restrictK.
by apply: contraTneq => ->; rewrite inE.
Qed.

Lemma in_Xi_small k n (S : {set 'I_k ^ n.+1}) (m : 'I_k) (s : 'I_k ^ n) :
  (s \in Xi m.+1 S) = (nthext S s m \in exts S s).
Proof. by rewrite in_exts nthextK leq_exts. Qed.

Lemma in_Xi_big k n (S : {set 'I_k ^ n.+1}) m (s : 'I_k ^ n) : m > k ->
  (s \in Xi m S) = false.
Proof. by rewrite ltnNge -leq_exts; apply/contraNF => /leq_trans ->. Qed.

(* Lemma in_Xi_index k n (S : {set 'I_k.+1 ^ n.+1}) (m : nat) (s : 'I_k.+1 ^ n) x : *)
(*    s \in Xi (indexext S s x) S. *)
(* Proof. *)
(* rewrite inE leq_ord. *)
(* Qed. *)

Lemma card_reext k n (S : {set 'I_k ^ n.+1}) (m : 'I_k) :
  #|reext S m| = #|Xi m.+1 S|.
Proof.
rewrite card_in_imset //= => x y xXi yXi /eqP.
by rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma card_extset (X : finType) n (S : {set X ^ n}) (x : X) :
  #|extset x S| = #|S|.
Proof.
by rewrite card_imset // => u v /eqP; rewrite eq_extelt => /andP [_ /eqP].
Qed.

(* Lemma mem_extset n (X : finType) (x x' : X) s (S : {set X ^ n}) : *)
(*   extelt x s \in extset x' S = (x == x') && (s \in S). *)
(* Proof. *)
(* apply/imsetP/idP => /= [[s' s'S /eqP]|/andP [/eqP<-]]; last by exists s. *)
(* by rewrite eq_extelt => /andP [-> /eqP ->]. *)
(* Qed. *)

Lemma mem_extset n (X : finType) (x : X) s (S : {set X ^ n}) :
  s \in extset x S = (s ord_max == x) && (restrict s \in S).
Proof.
apply/imsetP/idP => [[s' s'S ->]|/andP [/eqP<-] rsS]; first by rewrite !extE1.
by exists (restrict s) => //; rewrite !extE1.
Qed.

Lemma mem_extset_r n (X : finType) (x : X) s (S : {set X ^ n}) :
  extelt x s \in extset x S = (s \in S).
Proof. by rewrite mem_extset ?extE1. Qed.

(* Lemma exts_restrict_gt0 n (X : finType) (S : {set X ^ n.+1}) (s : X ^ n.+1) : *)
(*   (0 < #|exts S (restrict s)|) = (s \in S). *)
(* Proof.  *)
(* apply/card_gt0P; exists (s ord_max). *)
(* by rewrite inE restrictK. *)

Lemma restrict_inW n (X : finType) (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> restrict s \in Xi 1 S.
Proof.
by move=> sS; rewrite inE; apply/card_gt0P; exists (s ord_max); rewrite !extE1.
Qed.

Lemma restrict_in n k (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n.+1) :
  s \in S -> restrict s \in Xi (indexext S (restrict s) (s ord_max)).+1 S.
Proof. by move=> sS; rewrite inE -in_exts ?extE1. Qed.

Lemma extset0 n (X : finType) (x : X) : extset x set0 = set0 :> {set X ^ n.+1}.
Proof. by rewrite /extset imset0. Qed.

Lemma extsetK n (X : finType) (x : X) : cancel (@extset n _ x) (Xi 1).
Proof.
move=> S; apply/setP => /= s; apply/idP/idP => [|sS]; last first.
  by rewrite -[s](exteltK x) restrict_inW // mem_extset_r.
by rewrite inE => /card_gt0P [y]; rewrite inE mem_extset ?extE1 => /andP [].
Qed.

Lemma extset_eq0 n (X : finType) (x : X) (S : {set X ^ n}) :
  (extset x S == set0) = (S == set0).
Proof. by rewrite -(extset0 _ x) (can_eq (extsetK _)). Qed.

Lemma eq_extset n (X : finType) (x y : X) (S S' : {set X ^ n}) :
  (extset x S == extset y S') = ((S' != set0) ==> (x == y)) && (S == S').
Proof.
have [->|] /= := set_0Vmem S'; first by rewrite extset0 eqxx /= extset_eq0.
move=> [s sS']; have /set0Pn -> /= : exists s, s \in S' by exists s.
have [<-|/=] := altP (x =P y); first by rewrite (can_eq (extsetK _)).
apply: contraNF => /eqP eq_xS_yS'; have := mem_extset_r y s S'.
by rewrite -eq_xS_yS' sS' eq_sym mem_extset ?extE1 => /andP [].
Qed.

Lemma subset_ext n (X : finType) (x : X) (S S' : {set X ^ n}) :
  (extset x S \subset extset x S') = (S \subset S').
Proof.
apply/subsetP/subsetP => SS' s.
  by move/(mem_imset (extelt x))/SS'; rewrite mem_extset_r.
by case/imsetP=> s' s'S ->; rewrite mem_extset_r SS'.
Qed.

Lemma subset_Xi n (X : finType) m : {homo @Xi n X m : S S' / S \subset S'}.
Proof.
move=> S S' subSS'; apply/subsetP=> s; rewrite !in_set => /leq_trans-> //.
by apply/subset_leq_card/subset_exts.
Qed.

Lemma leq_Xi n (X : finType) (S : {set X ^ n.+1}) :
  {homo (@Xi _ _)^~ S : m p / (p <= m)%N >-> m \subset p}.
Proof. by move=> m p ?; apply/subsetP => s; rewrite !inE; apply/leq_trans. Qed.

Lemma reext_inj k n (S : {set 'I_k ^ n.+1}) :
  {in [pred m : 'I_k | Xi m.+1 S != set0] &, injective (reext S)}.
Proof.
move=> i j /= _ Xij_neq0; have /set0Pn [/= s'1 s'1Xi]:= Xij_neq0.
pose f k s := (extelt (nthext S s k) s) => /setP /(_ (f j s'1)).
rewrite (mem_imset (f j) s'1Xi) /f => /imsetP [/= s'2 s'2Xi] /eqP.
by rewrite eq_extelt andbC => /andP [/eqP -> /eqP /nthext_inj].
Qed.

Lemma subset_reext k n (S : {set 'I_k ^ n.+1}) m :
  reext S m \subset S.
Proof.
apply/subsetP=> i /imsetP [/= s' s'Xi ->].
by rewrite extelt_in nthext_in leq_exts.
Qed.

Lemma reext_eq0 k n (S : {set 'I_k.+1 ^ n.+1}) m :
  (reext S m == set0) = (Xi m.+1 S == set0).
Proof. by rewrite -!cards_eq0 card_reext. Qed.

Lemma Xi0s n (X : finType) S : Xi 0 S = [set: X ^ n].
Proof. by apply/setP => i; rewrite inE. Qed.

Lemma Xi0 n (X : finType) i : i > 0 -> Xi i (set0 : {set X ^ n.+1}) = set0.
Proof. by case: i => // i _; apply/setP => e; rewrite !inE exts0 cards0. Qed.

Lemma Xi1_eq0 n (X : finType) (S : {set X ^ n.+1}) :
  (Xi 1 S == set0) = (S == set0).
Proof.
apply/idP/idP=> [|/eqP->]; last by rewrite Xi0.
apply: contraTT => /set0Pn [x xS].
by apply/set0Pn; exists (restrict x); apply: restrict_inW.
Qed.

Lemma Xi_eq0  n (X : finType) (S : {set X ^ n.+1}) i :
  (Xi i.+1 S == set0) = [forall s, #|exts S s| <= i].
Proof.
apply/eqP/forallP => [XiiS_eq0 s|].
  apply: contra_eqT XiiS_eq0; rewrite -ltnNge => i_small.
  by apply/set0Pn; exists s; rewrite inE.
move=> few_s; apply: contraTeq isT => /set0Pn /= [s].
by rewrite inE ltnNge few_s.
Qed.

Lemma reext0 k n m : @reext k n set0 m = set0.
Proof.
apply/setP=> i; rewrite !inE; apply/negP => /imsetP /= [x].
by rewrite Xi0 ?inE.
Qed.

Lemma reextE k n (S : {set 'I_k.+1 ^ n.+1}) (m : 'I_k.+1) :
  reext S m = [set s in S | indexext S (restrict s) (s ord_max) == m].
Proof.
apply/setP => s; rewrite !inE; have [sS|sNS] /= := boolP (s \in S); last first.
  by apply:contraNF sNS; apply/subsetP/subset_reext.
apply/imsetP/eqP => /= [[s' s'Xi ->]|<-].
  by rewrite extelt_ord_max exteltK nthextK.
by exists (restrict s); rewrite ?in_Xi_small ?indexextK ?extE1.
Qed.

End Ext.

Definition extE := (extE1,mem_extset,indexextK,nthextK,extsetK,extset0).

(* Section Adapt. *)

(* Variables (k : nat). *)
(* Let X := 'I_k.+1. *)

(* Fixpoint adapt n : {set X ^ n} -> X ^ n -> 'I_k.+1 ^ n := *)
(*   if n isn't n.+1 then fun _ _ => [ffun _ => ord0] *)
(*   else fun S s => let s' := restrict s in *)
(*     extelt (indexext S s' (s ord_max)) *)
(*            (adapt (Xi 1 S) s'). *)

(* Fixpoint unadapt n : {set X ^ n} -> 'I_k.+1 ^ n -> X ^ n := *)
(*   if n isn't n.+1 then fun _ _ => [ffun _ => ord0] *)
(*   else fun S a => let a' := restrict a in *)
(*                   let s' := unadapt (Xi 1 S) a' in *)
(*     extelt (nthext S s' (a ord_max)) s'. *)

(* Lemma adaptK n (S : {set X ^ n}): {in S, cancel (adapt S) (unadapt S)}. *)
(* Proof. *)
(* elim: n => [|n IHn] in S * => s sS /=; apply/ffunP => i; rewrite ffunE //=. *)
(*   by case: i. *)
(* case: unliftP => [j|->] /=. *)
(*   by rewrite exteltK IHn ?restrict_inW // ffunE => <-. *)
(* rewrite exteltK extelt_ord_max ?IHn ?restrict_inW //. *)
(* by rewrite indexextK ?inE ?restrictK. *)
(* Qed. *)

(* Lemma unadaptK n (S : {set X ^ n}): {on S, cancel (unadapt S) & adapt S}. *)
(* Proof. *)
(* elim: n => [|n IHn] in S * => a /= uaS; apply/ffunP => /= i; rewrite ffunE //=. *)
(*   by case: i. *)
(* have := uaS => /restrict_inW; rewrite exteltK => uaXi. *)
(* case: unliftP => [j|->] /=; first by rewrite IHn // ?ffunE => <-. *)
(* by rewrite extelt_ord_max nthextK. *)
(* Qed. *)

(* Lemma adapt_bij n (S : {set X ^ n}) : {in S, bijective (adapt S)}. *)
(* Proof. by exists (unadapt S); [exact: adaptK|exact: unadaptK]. Qed. *)

(* (* Lemma adapt_sub n (S S' : {set X ^ n}) : S \subset S' -> *) *)
(* (*   {in S, adapt S =1 adapt S'}. *) *)
(* (* Proof. *) *)
(* (* elim: n => [|n IHn] //= in S S' * => subSSt s sS. *) *)
(* (* rewrite (IHn _ (Xi 1 S')) ?subset_Xi // ?restrict_in //. *) *)


(* End Adapt. *)

Section Signdet.

Definition Signs n := ('I_3 ^ n)%type.
Definition Expos n := ('I_3 ^ n)%type.

Definition sign (i : 'I_3) : int :=
  match val i with 0 => 0%R | 1 => 1%R | _ => -1%R end.

Definition expo (i : 'I_3) : nat :=
  match val i with 0 => 0%N | 1 => 1%N | _ => 2%N end.

Definition mat_coef n (i : Signs n) (j : Expos n) :=
  (\prod_k (sign (i k)) ^+ (expo (j k)))%:Q%R.

Definition mat n (S : {set Signs n}) (A : {set Expos n}) :=
  \matrix_(i < #|S|, j < #|A|) mat_coef (enum_val i) (enum_val j).

Definition adapted n (S : {set Signs n}) (A : {set Expos n}) :=
  (#|A| == #|S|) && row_free (mat S A).

Fixpoint adapt n (S : {set Signs n}) : {set Expos n} :=
  match n return {set Signs n} -> {set Expos n} with
    | 0     => fun S => S
    | n'.+1 => fun S => \bigcup_(i < 3) extset i (adapt (Xi i.+1 S))
  end S.
Arguments adapt n S0 : simpl never.

Lemma adapt0n (S : {set Signs 0}) : adapt S = S.
Proof. by []. Qed.

Lemma adaptSn n (S : {set Signs n.+1}) : 
  adapt S = \bigcup_(i < 3) extset i (adapt (Xi i.+1 S)).
Proof. by []. Qed.

Definition adaptE := (adapt0n, adaptSn).

Lemma subset_adapt n (S S' : {set Signs n}) :
  S \subset S' -> adapt S \subset adapt S'.
Proof.
elim: n => [//|n IHn] in S S' * => subSS' /=; apply/bigcupsP => i _.
by rewrite (bigcup_max i) // subset_ext IHn // subset_Xi.
Qed.

Lemma in_adapt  n (S : {set Signs n.+1}) (a : Expos n.+1) :
  (a \in adapt S) = (restrict a \in adapt (Xi (a ord_max).+1 S)).
Proof.
move=> /=; apply/bigcupP/idP => [[i _ /imsetP [s sAXi ->]]|].
  by rewrite ?extE.
by move=> ra; exists (a ord_max); rewrite ?extE.
Qed.

(* Definition mat n (S : {set Signs n}) : 'M[rat]_#|S| := *)
(*     \matrix_(i, j) mat_coef (enum_val i) (adapt S (enum_val j)). *)

(* Definition adapted n (S : {set Signs n}) := unitmx (mat S). *)

(* Lemma test (n : nat) : n > 4 -> False. *)
(* Proof. *)
(* move=> nnn. *)
(* have  [:iP] @i : 'I_n := Sub 2 iP. *)
(*   by rewrite 2?ltnW. *)

(* Lemma sub_adapt n (S S' : {set Signs n}) s : S \subset S' -> *)
(*   adapt S s = adapt S' s. *)

(* Lemma adapt_set n (S : {set Signs n.+1}) : *)
(*   adapt S @: S = \bigcup_(m < 3) extset m (adapt (Xi m.+1 S) @: (Xi m.+1 S)). *)
(* Proof. *)
(* apply/setP => i /=; apply/imsetP/bigcupP => /= [[s sS ->]|[x _]]. *)
(*   exists (indexext S (restrict s) (s ord_max)) => //. *)
(*   rewrite mem_extset eqxx andTb. *)
(*   have := restrict_in sS. *)
(*   rewrite reextE !inE !extelt_ord_max. *)
  
(*   rewrite extelt_in *)
  
(* rewrite in_bigcup. *)


(* Lemma subset_adapt n (S S' : {set Signs n}) : *)
(*   S \subset S' -> adapt S @: S \subset adapt S' @: S'. *)
(* Proof. *)
(* elim: n => [|n IHn] //= in S S' * => subSS' /=; *)
(* apply/subsetP => /= a /imsetP /= [s sS ->]; apply/imsetP => /=. *)
(*   by exists s => //; apply: subsetP sS. *)
(* set X := Xi _ S; set X' := Xi _ S'; have := IHn X X'. *)
(* rewrite subset_Xi // => /(_ isT) /subsetP /(_ (adapt X (restrict s))). *)
(* rewrite mem_imset ?restrict_in // => /(_ isT) /imsetP [/= s' s'X' ars]. *)
(* evar (x : 'I_3); exists (extelt x s'); last first. *)
(*   rewrite extelt_ord_max exteltK; congr (extelt _ _) => //. *)
(*   by apply: (can_inj (nthextK S' s')); rewrite indexextK; apply: erefl. *)
(* rewrite extelt_in nthext_in (@leq_trans #|exts S (restrict s)|) //. *)
(*   by rewrite -in_exts inE restrictK. *)
(* apply/subset_leq_card/subsetP => y; rewrite !inE => /(subsetP subSS'). *)


(* exists (extelt (nthext S (restrict s) (adapt S s ord_max)) s'); *)
(* rewrite ?extelt_ord_max ?exteltK /= ?indexextK. *)
(* rewrite extelt_in. *)
(*   rewrite extelt_in nthext_in /=. *)
  
(*   . *)
  
  
  
(* move=> subSS';  *)

(* elim: n => [//|n IHn] in S S' * => subSS' /=; apply/bigcupsP => i _. *)
(* by rewrite (bigcup_max i) // subset_ext IHn // subset_Xi. *)
(* Qed. *)

Lemma adapt_down_closed  n (S : {set Signs n}) (a b : Expos n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *.
  by move=> _; rewrite (fintype1 b) // card_ffun !card_ord.
move=> leq_ba; rewrite !in_adapt => raAXi.
have: restrict b \in adapt (Xi (a ord_max).+1 S).
  by apply: IHn raAXi => i; rewrite !ffunE leq_ba.
by apply: subsetP; rewrite subset_adapt ?leq_Xi ?ltnS ?leq_ba.
Qed.

Lemma ExposE n (S : {set Expos n.+1}) :
  S = \bigcup_(i < 3) reext S i.
Proof.
apply/setP => s; apply/idP/bigcupP => [sS|]; last first.
  move=> [i _ /imsetP [x]]; rewrite inE => i_small ->.
  by rewrite extelt_in nthext_in.
exists (indexext S (restrict s) (s ord_max)) => //.
by apply/imsetP; exists (restrict s); rewrite ?extE // -in_exts ?extE.
Qed.

Lemma noreext n (S : {set Expos n.+1}) (i : 'I_3) : 
  Xi i.+1 S = set0 -> reext S i = set0.
Proof. by move=> /eqP; rewrite -reext_eq0 => /eqP. Qed.

Lemma ExposED n (S : {set Expos n.+1}) :
  S = \bigcup_(i < 3 | Xi i.+1 S != set0) reext S i.
Proof.
rewrite [LHS]ExposE /= (bigID (fun i : 'I__ => Xi i.+1 S == set0)) /=.
by rewrite big1 ?set0U // => i; rewrite -reext_eq0 => /eqP.
Qed.

Lemma partition_Signs n (S : {set Signs n.+1}) :
  partition [set reext S (i : 'I__) | i in 'I_3 & Xi i.+1 S != set0] S.
Proof.
apply/and3P; split; [apply/eqP| |].
- symmetry; rewrite cover_imset [LHS]ExposED.
  by apply: eq_bigl => /= i; rewrite inE.
- apply/trivIsetP => /= _ _ /imsetP [i Xii_neq0 ->] /imsetP [j Xij_neq0 ->].
  rewrite !inE in Xii_neq0 Xij_neq0.
  rewrite (inj_in_eq (@reext_inj _ _ _)) ?inE //= => neq_ij.
  rewrite disjoints_subset; apply/subsetP => /= X /imsetP /= [x x_in ->].
  rewrite inE; apply/negP => /imsetP /= [y y_in] /eqP.
  rewrite !inE in x_in y_in; rewrite eq_extelt andbC => /andP [/eqP <-].
  by move=> /eqP /nthext_inj; apply/eqP.
apply/negP=> /imsetP [i]; rewrite inE => /andP [j /set0Pn [x xXi]].
move=> /setP /(_ (extelt (nthext S x i) x)); rewrite !inE.
by rewrite (mem_imset (fun s => extelt (nthext S s i) s)).
Qed.

Lemma adapt0 n : @adapt n set0 = set0.
Proof.
elim: n => [|n IHn] //=; rewrite adaptE big1 // => i _.
by rewrite Xi0 // IHn extset0.
Qed.

Lemma adapt_eq0 n X : (@adapt n X == set0) = (X == set0).
Proof.
elim: n => [|n IHn] // in X *.
apply/idP/idP => [/=|/eqP ->]; last by rewrite adapt0.
apply: contraTT; rewrite -Xi1_eq0 -IHn => /set0Pn [x x_adaX].
apply/set0Pn; exists (extelt ord0 x).
by apply/bigcupP; exists ord0 => //; rewrite !extE.
Qed.

Lemma partition_adapt n (S : {set Signs n.+1}) :
  partition [set extset i (adapt (Xi (i : 'I_3).+1 S))
            | i in 'I_3 & Xi i.+1 S != set0] (adapt S).
Proof.
apply/and3P => /=; split; [apply/eqP | |].
- rewrite adaptE (bigID [pred i : 'I__ | Xi i.+1 S == set0]) /=.
  rewrite big1 ?set0U; last by move=> i /eqP ->; rewrite adapt0 extset0.
  by rewrite cover_imset; apply: eq_bigl => i; rewrite inE.
- apply/trivIsetP => /= _ _ /imsetP [i _ ->] /imsetP [j _ ->].
  have [<-|neq_ij _] /= := altP (i =P j); first by rewrite eqxx.
  rewrite disjoints_subset; apply/subsetP => s.
  rewrite !inE => /imsetP /= [s' s'_adapt ->].
  by rewrite !extE negb_and neq_ij.
apply/negP=> /imsetP [i]; rewrite inE => Xi_neq0 /eqP.
by rewrite eq_sym extset_eq0 adapt_eq0; apply/negP.
Qed.

Lemma card_adapt n (S : {set Signs n}) : #|adapt S| = #|S|.
Proof.
elim: n => [//|n IHn] in S *.
rewrite (card_partition (partition_adapt S)).
rewrite (card_partition (partition_Signs S)).
rewrite !big_imset; last 2 first.
- move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0 eq_reext_ij.
  by apply/(@reext_inj _ _ S); rewrite ?inE.
- move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0.
  move=> /eqP; rewrite eq_extset -cards_eq0 IHn cards_eq0 Xij_neq0 /=.
  by move=> /andP [/eqP ? _].
apply: eq_bigr => i _; rewrite card_extset IHn card_imset //=.
by move=> s t /= /eqP; rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma prop1084 n (S : {set Signs n}) a :
 a \in adapt S -> 2 ^ #|[set i : 'I_n | a i != 0%R]| <= #|S|.
Proof.
move=> a_adapt.
pose B := [set b : Expos n | [forall i, (b i != ord0) ==> (b i == a i)]].
apply: (@leq_trans #|B|) => [{a_adapt}|]; last first.
  rewrite -(card_adapt S) subset_leq_card //; apply/subsetP => b.
  rewrite in_set => /forallP bP; apply: adapt_down_closed a_adapt => i.
  by have := bP i; rewrite implyNb => /orP [/eqP ->|/eqP ->].
suff -> : B = [set [ffun i => if i \in (I : {set _}) then a i else 0%R]
              | I in powerset [set i | a i != 0%R]].
  rewrite card_in_imset; first by rewrite card_powerset leqnn.
  move=> I J /=; rewrite !in_set => PI PJ eqIJ; apply/setP => i.
  have := congr1 (fun f : {ffun _ -> _} => f i == 0%R) eqIJ; rewrite !ffunE.
  have [] := (subsetP PI i, subsetP PJ i); rewrite in_set.
  case: (i \in I) => [/(_ isT) /negPf ->|_];
  by case: (i \in J) => // /(_ isT) /negPf ->.
apply/setP => b; rewrite in_set.
apply/'forall_implyP/imsetP => [bP|[I]]; last first.
  by rewrite powersetE => /subsetP IP -> i; rewrite !ffunE; case: ifP.
exists [set i | b i != 0%R].
  rewrite powersetE; apply/subsetP => i; rewrite !in_set => b_neq0.
  by rewrite -(eqP (bP _ _)).
apply/ffunP => i; rewrite ffunE in_set.
by case: ifPn => [/bP /eqP <- //|]; rewrite negbK => /eqP.
Qed.

Lemma enum_rank_in_id (T : finType) (x0 : T)
  (A : pred T) (Ax0 : x0 \in A) (x : T) :
  (enum_val (enum_rank_in Ax0 x) == x) = (x \in A).
Proof.
by apply/eqP/idP => [<-|xA]; rewrite ?enum_valP ?enum_rankK_in ?eqxx.
Qed.


(* Lemma adapt_adapted1 (S : {set Signs 1}) : row_free (mat S (adapt S)). *)
(* Proof. *)
(* have [->|SN0] /= := altP (S =P set0). *)
(*   by move: (mat _ _); rewrite cards0 => M; rewrite flatmx0 -row_leq_rank. *)
(* apply/row_freeP. *)
(* Admitted. *)

(* Definition mat1 (S : {set Signs 1}) := *)
(*   projT1 (sig_eqW (row_freeP (adapt_adapted1 S))). *)

(* Lemma mat1P (S : {set Signs 1}) : mat S (adapt S) *m mat1 S = 1%:M. *)
(* Proof. by rewrite /mat1; case: sig_eqW. Qed. *)

Lemma row_free_1ext (S : {set 'I_3}) : 'M[rat]_#|S| :
  row_free (\matrix_(i, j) sign (enum_val i) ^+ expo (inord j)).

Lemma adapt_adapted n (S : {set Signs n}) : adapted S (adapt S).
Proof.
rewrite /adapted {1}card_adapt eqxx /=.
elim: n => [|n IHn] in S *.
  apply/row_freeP; exists 1%:M; rewrite mulmx1.
  apply/matrixP=> i j; rewrite !mxE /mat_coef big_ord0.
  have /orP [/eqP S0|/eqP S1] : (#|S| == 0) || (#|S| == 1).
  - have := subset_leq_card (subsetT S).
    by rewrite cardsT card_ffun !card_ord expn0; move: #|S|=> [|[]].
  - by have := i; rewrite {1}S0 => [] [].
  - by rewrite (fintype1 i) ?card_ord ?eqxx.
apply/row_freeP; have /row_freeP [M MP] := IHn (Xi 1 S).
have [|SN0] := eqVneq S set0.
  admit.
have /set0Pn [s s_in] := SN0.
pose i_s := enum_rank_in s_in s.
have /set0Pn [a a_in] : adapt S != set0.
  by rewrite adapt_eq0.
pose i_a := enum_rank_in a_in a.
have [|Xi1_neq0] := eqVneq (Xi 1 S) set0.
  admit.
have := Xi1_neq0; rewrite -adapt_eq0 => aXi1_neq0.
(* have :=  *)
have /set0Pn [s' s'_in] := Xi1_neq0.
have /set0Pn [a' a'_in] := aXi1_neq0.
(* have /set0Pn [a a_in]: adapt S != set0. *)
(*   rewrite adapt_eq0. *)
(*   admit. *)
exists (\matrix_(j,k) M (enum_rank_in a'_in (restrict (enum_val j)))
                        (enum_rank_in s'_in (restrict (enum_val k)))
 *                         
                        ).
apply/matrixP => /= i k; rewrite !mxE.
(* pose F j := ((mat S (adapt S)) i (insubd i_a j) * N (insubd i_a j) k)%R. *)
set F := BIG_F.
pose P a' := a' \in adapt (Xi 1 S).
pose Q a' x := x \in exts (adapt S) a'.
transitivity (\sum_(p : Expos n * 'I_3 | P p.1 && Q p.1 p.2)
               F (enum_rank_in a_in (extelt p.2 p.1)))%R.
  symmetry.
  rewrite (reindex (fun j : 'I_#|adapt S| => let a := enum_val j in
                   (restrict a, a ord_max))) => /=.
    apply: eq_big => /= j; rewrite /P /Q !extE enum_valP ?enum_valK_in //.
    have := (enum_valP j); rewrite ?andbT in_adapt.
    exact/subsetP/subset_adapt/leq_Xi.
  exists (fun a : Expos n * 'I_3 => enum_rank_in a_in (extelt a.2 a.1)).
    by move=> j /=; rewrite !extE ?enum_valK_in.
  move=> [b' x]; rewrite /P /Q ?extE => /andP [/= Pb Qb].
  by rewrite enum_rankK_in ?extE //=.
set G := BIG_F; rewrite /= in G *; pose G' a b := G (a, b).
rewrite (eq_bigr (fun p => G' p.1 p.2)); do ?by case.
rewrite -pair_big_dep /=.

  rewrite inE in Qb.
  move: Pb'
  rewrite in_adapt
    rewrite in_adapt ?extE.
    apply: subsetP Pb.
    rewrite subset_adapt //.
      
       have := en
       rewrite in_adapt.
       set b := enum_val j.
       rewrite 
       rewrite 
   
rewrite (eq_bigr (fun j : 'I__ => F j)); last first.
  by move=> j _; rewrite /F !insubd_id.
rewrite [LHS](@big_ord_widen _ _ _ #|adapt S| #|Expos n.+1| F); last first.
  exact/subset_leq_card/subset_predT.
rewrite (reindex (fun a : Expos n * Expos 1 =>
  enum_rank_in a_in (extelt (a.2 ord0) a.1))); last first.
  exists (fun j => let a := enum_val j in
                   (restrict a, [ffun _ => a ord_max])) => /=.
    move=> [b' x] /=; rewrite -topredE /= => enum_rank_small.
    rewrite enum_rankK !extE; congr (_, _).
    by apply/ffunP => j; rewrite ffunE !ord1.
  move=> j; rewrite -topredE /= => j_small.
  by rewrite ffunE !extE enum_valK.
set G := BIG_F; rewrite /= in G *; pose G' a b := G (a, b).
rewrite (eq_bigr (fun p => G' p.1 p.2)); do ?by case.
rewrite (eq_bigl (fun p => P p.1 && Q p.1 p.2)); last first.
  move=> [a' x] /=; rewrite /P /Q.
  
rewrite -(pair_big_dep predT Q' G') /=.
    
    
    

rewrite (reindex (enum_rank_in a_in)); last first.
  exists enum_val => s. 
    rewrite enum_rankK_in.

rewrite (reindex (fun i : 'I_#|adapt (Xi 1 S)| * 'I_ =>
  enum_rank_in a_in (extelt (a.2 ord0) a.1))); last first.
  exists (fun a : 'I_#|adapt S| =>
         (restrict a, [ffun _ : 'I_1 => a ord_max])).
  e



exists (\matrix_(j,k) let (a, t) := (enum_val j, enum_val k) in
  (M (enum_rank_in a'_in (restrict a))
    (enum_rank_in s'_in (restrict t))
  * mat1 [set [ffun _ => s] | s in exts S (restrict t)] j k)%R).

End SignDet.

