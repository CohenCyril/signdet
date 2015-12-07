From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
From mathcomp Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint rat tuple.
From mathcomp Require Import interval matrix mxtens mxalgebra binomial.
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

Section SignDet.

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

(* The nth, last element of the extension of s in S *)
Definition nthext k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) (m : nat) :
  'I_k.+1 := nth ord0 (sort (fun m n : 'I__ => m <= n) (enum (exts S s))) m.

(* the inverse of nthext *)
Definition indexext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) (i : 'I_k) : nat :=
  index i (sort (fun m n : 'I__ => m <= n) (enum (exts S s))).

(* the set of elements with at least m extensions in S,
  Xi 1 is the inverse of restrict *)
(* Definition Xi n (X : finType) (m : nat) (S : {set X ^ n.+1}) : {set X ^ n}:= *)
(*   [set s : X ^ n | [exists (E : {set X} | #|E| == m),  *)
(*                     forall x in E, extelt x s \in S]]. *)
Definition Xi n (X : finType) (m : nat) (S : {set X ^ n.+1}) : {set X ^ n}:=
  [set s : X ^ n | m <= #|exts S s|].

(* The nth extension in S *)
Definition reext k n (S : {set 'I_k.+1 ^ n.+1}) (m : nat) :
  {set 'I_k.+1 ^ n.+1} :=
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

Lemma eq_extelt n (X : finType) (x x' : X) (s s' : X ^ n) :
  (extelt x s == extelt x' s') = (x == x') && (s == s').
Proof.
have [->|] /= := altP (x =P x'); first by rewrite (can_eq (exteltK _)).
apply: contraNF => /eqP /(congr1 (fun u : _ ^ _ => u ord_max)).
by rewrite !extelt_ord_max => ->.
Qed.

Lemma exts0 n (X : finType) (s : X ^ n) : exts set0 s = set0.
Proof. by apply/setP=> i; rewrite !inE. Qed.

Lemma ltn_indexext k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) x :
  x \in exts S s -> indexext S s x < #|exts S s|.
Proof.
rewrite /indexext; set l := sort _ _ => xS.
rewrite (_ : #|exts S s| = size l) ?index_mem ?cardE ?size_sort //.
by rewrite mem_sort mem_enum.
Qed.

Lemma nthextK k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) :
  {in [pred i | i < #|exts S s|], cancel (nthext S s) (indexext S s)}.
Proof.
move=> i iS; apply: index_uniq; rewrite ?sort_uniq ?enum_uniq //.
by rewrite size_sort -cardE.
Qed.

Lemma indexextK k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) :
  {in exts S s, cancel (indexext S s) (nthext S s)}.
Proof. by move=> i iS; apply: nth_index; rewrite mem_sort mem_enum. Qed.

Lemma nthext_inj k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) :
  {in [pred i | i < #|exts S s|] &, injective (nthext S s)}.
Proof. exact: can_in_inj (@nthextK _ _ _ _). Qed.

Lemma nthextP k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) x :
  reflect (exists2 i, i < #|exts S s| & nthext S s i = x)
          (x \in exts S s).
Proof.
rewrite /nthext; set l := sort _ _.
have -> : #|exts S s| = size l by rewrite size_sort -cardE.
suff -> : x \in exts S s = (x \in l) by exact: nthP.
by rewrite mem_sort mem_enum.
Qed.

Lemma in_nthext k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) (i : nat) :
  i < #|exts S s| -> nthext S s i \in exts S s.
Proof. by move=> i_small; apply/nthextP; exists i. Qed.

Lemma subset_exts (X : finType) n (s : X ^ n) :
  {homo (fun S => exts S s) : S S' / S \subset S'}.
Proof.
by move=> S S' /subsetP SsubS'; apply/subsetP => x; rewrite !inE => /SsubS'.
Qed.

Lemma exts_restrict_neq0 (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> exts S (restrict s) != set0.
Proof.
move=> sS; have : s ord_max \in exts S (restrict s).
  by rewrite inE ?restrictK.
by apply: contraTneq => ->; rewrite inE.
Qed.

Lemma card_exts (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) :
  #|exts S s| <= #|X|.
Proof. by rewrite subset_leq_card //; apply/subsetP. Qed.

Lemma nthext_in k n (S : {set 'I_k.+1 ^ n.+1}) (m : nat) (s : 'I_k.+1 ^ n) :
   s \in Xi m S -> forall i, i < m -> extelt (nthext S s i) s \in S.
Proof.
by rewrite inE => m_small i /leq_trans /(_ m_small) /in_nthext; rewrite inE.
Qed.

Lemma card_reext k n (S : {set 'I_k.+1 ^ n.+1}) (m : nat) :
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

Lemma mem_extset n (X : finType) (x x' : X) s (S : {set X ^ n}) :
  extelt x s \in extset x' S = (x == x') && (s \in S).
Proof.
apply/imsetP/idP => /= [[s' s'S /eqP]|/andP [/eqP<-]]; last by exists s.
by rewrite eq_extelt => /andP [-> /eqP ->].
Qed.

Lemma mem_extset_r n (X : finType) (x : X) s (S : {set X ^ n}) :
  extelt x s \in extset x S = (s \in S).
Proof. by rewrite mem_extset eqxx. Qed.

(* Lemma exts_restrict_gt0 n (X : finType) (S : {set X ^ n.+1}) (s : X ^ n.+1) : *)
(*   (0 < #|exts S (restrict s)|) = (s \in S). *)
(* Proof.  *)
(* apply/card_gt0P; exists (s ord_max). *)
(* by rewrite inE restrictK. *)

Lemma restrict_in n (X : finType) (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> restrict s \in Xi 1 S.
Proof.
move=> sS; rewrite inE; apply/card_gt0P; exists (s ord_max).
by rewrite inE restrictK.
Qed.

Lemma extset0 n (X : finType) (x : X) : extset x set0 = set0 :> {set X ^ n.+1}.
Proof. by rewrite /extset imset0. Qed.

Lemma extsetK n (X : finType) (x : X) : cancel (@extset n _ x) (Xi 1).
Proof.
move=> S; apply/setP => /= s; apply/idP/idP => [|sS]; last first.
  by rewrite -[s](exteltK x) restrict_in // mem_extset_r.
by rewrite inE => /card_gt0P [y]; rewrite inE mem_extset => /andP [].
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
by rewrite -eq_xS_yS' sS' eq_sym mem_extset => /andP [].
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

Lemma reext_inj k n (S : {set 'I_k.+1 ^ n.+1}) :
  {in [pred m | Xi m.+1 S != set0] &, injective (reext S)}.
Proof.
move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0.
have [// ? ?|neq_ij] := altP (i =P j).
wlog lt_ji : i j Xii_neq0 Xij_neq0 neq_ij / j < i => [hwlog|].
  have := neq_ij; rewrite neq_ltn => /orP [|/hwlog]; last exact.
  move=> /hwlog hwlogji eqXij; symmetry.
  by apply: hwlogji; rewrite // 1?eq_sym.
have /set0Pn [s sXi]:= Xij_neq0.
pose f k s := extelt (nthext S s k) s.
move=> /setP /(_ (f j s)); rewrite (mem_imset (f j) sXi).
move=> /imsetP [s' s'Xi] /eqP; rewrite eq_extelt andbC => /andP [/eqP eq_ss'].
by rewrite eq_ss' !inE in s'Xi sXi * => /eqP /nthext_inj ->; rewrite // !inE.
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
by apply/set0Pn; exists (restrict x); apply: restrict_in.
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

Definition Signs n := ('I_3 ^ n)%type.
Definition Expos n := ('I_3 ^ n)%type.

Definition sign (i : 'I_3) : int :=
  match val i with 0 => 0%R | 1 => 1%R | _ => -1%R end.

Definition expo (i : 'I_3) : nat :=
  match val i with 0 => 0%N | 1 => 1%N | _ => 2%N end.

Definition mat_coef n (i : Signs n) (j : Expos n) :=
  (\prod_k (sign (i k)) ^+ (expo (j k)))%:Q%R.

Definition mat n (s : {set Signs n}) (a : {set Expos n}) :
  'M[rat]_(#|s|, #|a|) :=
    \matrix_(i,j) mat_coef (enum_val i) (enum_val j).

Definition adapted n (s : {set Signs n}) (a : {set Expos n}) :=
  (#|s| == #|a|) && row_free (mat s a).

Fixpoint adapt n (S : {set Signs n}) : {set Expos n} :=
  match n return {set Signs n} -> {set Expos n} with
    | 0     => fun S => S
    | n'.+1 => fun S => \bigcup_(i < 3) extset i (adapt (Xi i.+1 S))
  end S.

Lemma adapt_monotonic n (S S' : {set Signs n}) :
  S \subset S' -> adapt S \subset adapt S'.
Proof.
elim: n => [//|n IHn] in S S' * => subSS' /=; apply/bigcupsP => i _.
by rewrite (bigcup_max i) // subset_ext IHn // subset_Xi.
Qed.

Lemma in_adapt  n (S : {set Signs n.+1}) (a : Expos n.+1) :
  (a \in adapt S) = (restrict a \in adapt (Xi (a ord_max).+1 S)).
Proof.
move=> /=; apply/bigcupP/idP => [[i _ /imsetP [s sAXi ->]]|].
  by rewrite exteltK extelt_ord_max.
by move=> raAXi; exists (a ord_max); rewrite // -{1}[a]restrictK mem_extset_r.
Qed.

Lemma adapt_down_closed  n (S : {set Signs n}) (a b : Expos n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *.
  by move=> _; rewrite (fintype1 b) // card_ffun !card_ord.
move=> leq_ba; rewrite !in_adapt => raAXi.
have: restrict b \in adapt (Xi (a ord_max).+1 S).
  by apply: IHn raAXi => i; rewrite !ffunE leq_ba.
by apply: subsetP; rewrite adapt_monotonic ?leq_Xi ?ltnS ?leq_ba.
Qed.

Lemma ExposE n (S : {set Expos n.+1}) :
  S = \bigcup_(i < 3) reext S i.
Proof.
apply/setP => s; apply/idP/bigcupP => [sS|]; last first.
  move=> [i _ /imsetP [x x_in ->]].
  by rewrite (nthext_in x_in).
exists (insubd ord0 (indexext S (restrict s) (s ord_max))) => //.
rewrite insubdK; last first.
  rewrite -topredE /= (leq_trans (ltn_indexext _)) //=.
    by rewrite inE restrictK.
  by rewrite (leq_trans (card_exts _ _)) ?card_ord.
apply/imsetP; exists (restrict s).
  by rewrite ?inE ?ltn_indexext //= ?inE ?restrictK.
by rewrite indexextK ?inE ?restrictK.
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
  rewrite !inE in x_in y_in; rewrite eq_extelt andbC => /andP [/eqP eq_xy].
  rewrite -eq_xy {y eq_xy} in y_in *.
  rewrite (inj_in_eq (@nthext_inj _ _ _ _)) ?inE -?card_extsP //.
  exact/negP.
apply/negP=> /imsetP [i]; rewrite inE => /andP [j /set0Pn [x xXi]].
move=> /setP /(_ (extelt (nthext S x i) x)); rewrite !inE.
by rewrite (mem_imset (fun s => extelt (nthext S s i) s)).
Qed.

Lemma adapt0 n : @adapt n set0 = set0.
Proof.
elim: n => [|n IHn] //=; rewrite big1 // => i _.
by rewrite Xi0 // IHn extset0.
Qed.

Lemma adapt_eq0 n X : (@adapt n X == set0) = (X == set0).
Proof.
elim: n => [|n IHn] // in X *.
apply/idP/idP => [/=|/eqP ->]; last by rewrite adapt0.
apply: contraTT; rewrite -Xi1_eq0 -IHn => /set0Pn [x x_adaX].
apply/set0Pn; exists (extelt ord0 x).
by apply/bigcupP; exists ord0 => //; rewrite mem_extset eqxx /=.
Qed.

Lemma partition_adapt n (S : {set Signs n.+1}) :
  partition [set extset i (adapt (Xi (i : 'I_3).+1 S))
            | i in 'I_3 & Xi i.+1 S != set0] (adapt S).
Proof.
apply/and3P => /=; split; [apply/eqP | |].
- rewrite (bigID [pred i : 'I__ | Xi i.+1 S == set0]) /=.
  rewrite big1 ?set0U; last by move=> i /eqP ->; rewrite adapt0 extset0.
  by rewrite cover_imset; apply: eq_bigl => i; rewrite inE.
- apply/trivIsetP => /= _ _ /imsetP [i _ ->] /imsetP [j _ ->].
  have [<-|neq_ij _] /= := altP (i =P j); first by rewrite eqxx.
  rewrite disjoints_subset; apply/subsetP => s.
  rewrite !inE => /imsetP /= [s' s'_adapt ->].
  by rewrite mem_extset negb_and neq_ij.
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
  by apply: val_inj; apply: (@reext_inj _ _ S); rewrite ?inE.
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

(* Lemma rowfree_matP n (S : {set Signs n}) (E : {set Expos n}) : *)
(*   #|S| = #|E| -> *)
(*   reflect (forall v : Signs n -> rat, *)
(*           (forall e : Expos n, e \in E -> *)
(*           (\sum_(s in S) v s * mat_coef s e = 0)%R) -> *)
(*             forall s : Signs n, s \in S -> v s = 0%R) *)
(*           (row_free (mat S E)). *)
(* Proof. *)
(* have [->|/set0Pn /sigW [s0 s0S]] := eqVneq S set0. *)
(*   move: (mat _ _); rewrite cards0 => M _; rewrite flatmx0. *)
(*   apply: (iffP (row_freeP))=> [_ ? ? ?|*]. *)
(*     by rewrite inE. *)
(*   by exists 0%R; rewrite mulmx0 flatmx0. *)
(* have [{1}->|/set0Pn /sigW [e0 e0E] _] := eqVneq E set0. *)
(*   rewrite cards0 => /eqP; rewrite cards_eq0 => /eqP S_eq0. *)
(*   by rewrite S_eq0 inE in s0S. *)
(* apply: (iffP idP) => [/row_freeP [M MP] v vP s sS|]. *)
(*   have := MP. *)
(*   move=> /(congr1 (mulmx (\row_(i < #|S|) v (enum_val i)))). *)
(*   rewrite mulmxA mulmx1 => /rowP /(_ (enum_rank_in sS s)). *)
(*   rewrite !mxE enum_rankK_in // => <-. *)
(*   rewrite (reindex_onto (enum_rank_in e0E) enum_val) //=; last first. *)
(*     by move=> i; rewrite enum_valK_in. *)
(*   rewrite (eq_bigl _ _ (enum_rank_in_id _)). *)
(*   rewrite big1 => //= e _; rewrite !mxE. *)
(*   rewrite (reindex_onto (enum_rank_in sS) enum_val) //=; last first. *)
(*     by move=> i; rewrite enum_valK_in. *)
(*   rewrite (eq_bigl _ _ (enum_rank_in_id _)). *)
(*   pose e' := enum_val (enum_rank_in e0E e). *)
(*   have e'E : e' \in E by apply: enum_valP. *)
(*   set x := (X in (X * _)%R); suff -> : x = 0%R by rewrite mul0r. *)
(*   rewrite -[RHS](vP e') //; apply: eq_bigr => s' s'S. *)
(*   by rewrite !mxE -/e' enum_rankK_in. *)
(* move=> matcoefP. *)
(* suff: forall (L : 'rV__), L *m mat S E = 0%R -> L = 0%R. *)
(*   move=> Hmat; rewrite -kermx_eq0; apply/eqP. *)
(*   apply/row_matrixP => i; rewrite row0; apply/Hmat. *)
(*   by apply/sub_kermxP; rewrite row_sub. *)
(* move=> L. *)
(* pose v := [ffun s : Signs n => L ord0 (enum_rank_in s0S s)]. *)
(* have -> : L = \row_i v (enum_val i). *)
(*   by apply/rowP => i; rewrite !mxE ffunE enum_valK_in. *)
(* move=> vM_eq0; apply/rowP => i; rewrite !mxE. *)
(* apply: matcoefP => //; last exact: enum_valP. *)
(* move=> e eE; have /rowP /(_ (enum_rank_in eE e)):= vM_eq0; rewrite !mxE. *)
(* rewrite (reindex_onto (enum_rank_in s0S) enum_val) //=; last first. *)
(*   by move=> j; rewrite enum_valK_in. *)
(* rewrite (eq_bigl _ _ (enum_rank_in_id _)) => S_eq0; rewrite -[RHS]S_eq0. *)
(* apply: eq_bigr => s sS; rewrite !mxE. *)
(* by rewrite !enum_rankK_in. *)
(* Qed. *)

(* Lemma adaptedP n (S : {set Signs n}) : *)
(*   reflect (forall v : Signs n -> rat, *)
(*           (forall e : Expos n, e \in adapt S -> *)
(*           (\sum_(s in S) v s * mat_coef s e = 0)%R) -> *)
(*             forall s : Signs n, s \in S -> v s = 0%R) *)
(*           (adapted S (adapt S)). *)
(* Proof. *)
(* rewrite /adapted [in X in reflect _ (X && _)]card_adapt eqxx /=. *)
(* by apply: rowfree_matP; rewrite card_adapt. *)
(* Qed. *)

(* Lemma adapt_adapted1 (S : {set Signs 1}) : adapted S (adapt S). *)
(* Proof. *)
(* rewrite /adapted {1}card_adapt eqxx. *)
(* have [->|SN0] /= := altP (S =P set0). *)
(*   by move: (mat _ _); rewrite cards0 => M; rewrite flatmx0 -row_leq_rank. *)
(* apply/row_freeP. *)
(* Admitted. *)

(* Ltac grab_proj proj d v i := *)
(*   match v with *)
(*   | context C[proj d] => *)
(*       let v := context C[i] in *)
(*       grab_proj proj d v i || exact: v *)
(*   end. *)

(* Ltac fill_grab_proj proj d f i := *)
(*   let fbody := eval lazy beta in (f d) in *)
(*   grab_proj proj d fbody i. *)

(* Ltac help_HO_proj proj f nf := *)
(*   let ty := type of f in let ty := eval hnf in ty in *)
(*   let typroj := type of proj in let typroj := eval hnf in typroj in *)
(*   let fbody := eval unfold f in f in let fbody := eval hnf in fbody in *)
(*   match fbody with fun id => _ => *)
(*   match ty with ?SRC -> ?TGT => match typroj with _ -> ?NEWSRC => *)
(*     let d := fresh "dummy" in *)
(*     let nfbody := fresh in *)
(*     let spill := fresh nf in *)
(*     let i := fresh id in *)
(*     (have [: spill ] _ (d : SRC) : True by ( *)
(*       (have @nfbody (i : NEWSRC) : TGT by fill_grab_proj proj d fbody i); *)
(*       (suff: phantom _ nfbody by []); *)
(*       abstract: spill @nfbody; (* if d occurs in nfbody, abstract: fails *) *)
(*       exact: Phantom)); *)
(*     lazy zeta in spill; move: spill; set nf := (F in phantom _ F) => _ *)
(*   end end end. *)

Lemma adapt_adapted n (S : {set Signs n}) : adapted S (adapt S).
Proof.
elim: n => [|n IHn] in S *.
  rewrite /adapted /= eqxx.

apply/adaptedP; elim: n {-2}n (leqnn n) => [|N IHN] n n_small in S *.
  do [move: n_small; rewrite leqn0 => /eqP ->] in S *.
  move=> v vP s sS; have card30 : #|{: 'I_3 ^ 0}| = 1.
    by rewrite card_ffun !card_ord expn0.
  have /= := (vP s); rewrite sS => /(_ isT); have -> : S = [set s].
    by apply/setP => x; rewrite !(fintype1 s) // !inE eqxx.
  by rewrite big_set1 /mat_coef big_ord0 mulr1.
move: n_small S; rewrite leq_eqVlt => /predU1P [-> S|]; last exact: IHN.
move=> v vP s sS; rewrite -(restrictK s).
pose v' s' (x : Signs 1) := v (extelt (x ord_max) s').
suff: v' (restrict s) [ffun=> s ord_max] = 0%R by rewrite /v' ffunE.
pose S1 s' : {set Expos 1} := [set [ffun=> x] | x in exts S s'].
apply: (adaptedP (S1 (restrict s)) (adapt_adapted1 _)); last first.
  by apply/imsetP; exists (s ord_max); rewrite ?ord_max_in_exts.
move=> a a_in.
evar (v'' : Signs N -> rat); transitivity (v'' (restrict s)).
  by rewrite /v''; move: (restrict _) => //.
pose m := #|exts S (restrict s)|.-1.
have m_small : m < #|exts S (restrict s)|.
  by rewrite prednK // -card_extsP restrict_in //.
apply: (IHN _ _ (Xi S m.+1)) => //; last first.
  by rewrite card_extsP.
  (* by rewrite restrict_in. *)
move=> e e_in; rewrite /v'' /S1.
evar (G : 'I_3 ^ N -> rat); rewrite (eq_bigr G); last first.
  by move=> i i_in; rewrite mulr_suml /G.
rewrite pair_big_dep /=.
rewrite (reindex (fun s => (restrict s, [ffun=> s ord_max]))) /=; last first.
  exists (fun p : Expos N * Expos 1 => extelt (p.2 ord_max) p.1) => /=.
    by move=> t /=; rewrite ffunE restrictK.
  move=> [t1 t2] _ /=; rewrite !ffunE unlift_none /=.
  by rewrite exteltK; congr (_, _); apply/ffunP=> i; rewrite ffunE !ord1.
rewrite -[RHS](vP (extelt (a ord_max) e)); last first.
  rewrite -(cover_partition (partition_adapt _)).
  apply/bigcupP => /=.
  exists (extset (a ord_max) (adapt (Xi S (a ord_max).+1))); last first.
    admit.
  admit.
  (*   rewrite  *)
  (* apply/imsetP. exists (a ord_max) => //=. last first. *)
  (*   rewrite mem_extset. *)
  (*   rewrite inE /=; apply/set0Pn.  *)
  (*   exists (restrict s); rewrite card_extsP. *)
  (* rewrite mem_extelt. *)


  (* pose i := #|exts S (restrict s)|.-1. *)
  (* have i_small : i < #|exts S (restrict s)|. *)
  (*   by rewrite prednK // -card_extsP restrict_in //. *)
  (* exists (extset (Ordext i_small) (adapt (Xi S i.+1))). *)
  (* apply/imsetP; exists (Ordext i_small) => //=. *)
  (*   rewrite inE /=; apply/set0Pn.  *)
  (*   by exists (restrict s); rewrite card_extsP. *)
  (* rewrite mem_extelt. *)
  (* move: a_in. *)
  (* rewrite /S1 /ex. *)
  (* admit. *)
apply: eq_big => t.
  have [tS|tNS] := boolP (t \in S).
    (* rewrite -card_extsP. *)
    rewrite restrict_in //=.
    by apply/imsetP; exists (t ord_max); rewrite // extsP restrictK.
  apply/negP => /andP [_ /imsetP [x xt_eq] //].
  move=> /(congr1 (fun f : {ffun _ -> _} => f ord0)); rewrite !ffunE => x_eq.
  by rewrite -x_eq extsP restrictK (negPf tNS) in xt_eq.
move=> /andP [t_in _].
rewrite /v' ffunE restrictK /mat_coef.
rewrite !big_ord_recr /= big_ord0 mul1r ffunE extelt_ord_max mulrAC.
rewrite rmorphM /= mulrA; congr (_ * _%:~R * _)%R.
apply: eq_bigr => i _ /=.
congr (sign _ ^+ expo _); apply: val_inj => //=.
  by rewrite /restrict ffunE //= lift_ord_max.
by rewrite -{1}[e](exteltK (a ord_max)) /restrict ffunE lift_ord_max.
Qed.

End SignDet.
