Require Import Arith.
Require Import Zee.vals.
Require Import Zee.dec Zee.maplike.
Require Import Lia.
Require Import String.

Section Frame.
  Context {A : Set}.
  Definition V := @V A.
  Definition SecTyV := @SecTyV A.
  
(*  Definition Lab := @Lab A.
  Definition Ty := @Ty A.
  Definition LabVar := @LabVar A.
  Definition SecTy := @SecTy A.
  Definition AtomSecTy := @AtomSecTy A.
*)
  
  Definition Range : Type := nat * nat.
  Opaque Range.

  Class HasRange (A : Type) :=
    {
      dom: A -> Range
    }.
  Hint Constructors HasRange.

  Global Instance HasRange_Range : HasRange Range.
  Proof.
    constructor.
    eapply id.
  Defined.
  
  Definition in_range {T : Type} `{HasRange T} (n : nat) (x : T) : Prop :=
    let (n1, n2) := dom x in n1 <= n /\ n <= n1 + n2.
  Hint Unfold in_range.
  
  Infix "∈" := in_range (at level 70).
  Infix "∉" := (fun n r => not (in_range n r)) (at level 80).

  Lemma in_range_dec {T : Type} `{HasRange T} n r:
    { n ∈ r } + { n ∉ r }.
  Proof.
    destruct (dom r) as [n1 n2] eqn:?H.
    unfold in_range.
    rewrite -> H0.
    destruct (le_dec n1 n).
    - destruct (le_dec n (n1 + n2)).
      + left.
        split; assumption.
      + right.
        intro.
        eapply n0.
        eapply (proj2 H1).
    - right.
      intro.
      eapply n0.
      eapply (proj1 H1).
  Defined.

  Class HasVersion (A : Type) :=
    {
      version: A -> Version
    }.
  Hint Constructors HasVersion.
  
  Record EFrame (M : Type) `{MapLike M nat V} :=
    {
      range_of : Range;
      mem_of : M;
      version_of: Version
    }.
  Hint Constructors EFrame.
  Global Arguments Build_EFrame { _ } { _ }.
  Global Arguments range_of { _ } { _ }.
  Global Arguments mem_of { _ } { _ }.
  Global Arguments version_of { _ } { _ }.
  
  Global Instance HasRange_EFrame {M : Type} `{MapLike M nat V} :
    HasRange (EFrame M) := {}.
  intros.
  eapply (dom (range_of X)).
  Defined.

  Global Instance HasVersion_EFrame {M : Type} `{MapLike M nat V} :
    HasVersion (EFrame M) := {}.
  intros.
  eapply (version_of X).
  Defined.
  
  Global Instance ReadableMapLike_EFrame {M : Type} `{MapLike M nat V} :
    ReadableMapLike (EFrame M) nat V := {}.
  - intros efr n.
    eapply (mem_of efr ? n).
  - eapply (Build_EFrame (0, 0) ∅ 0).
  - intros.
    simpl.
    eapply lookup_empty_map.
  Defined.

  Global Instance WriteableMapLike_EFrame {M : Type} `{MapLike M nat V} :
    WriteableMapLike (EFrame M) nat V := {}.
  intros n v efr.
  eapply (Build_EFrame (dom efr) (mem_of efr [n ↦ v]) (version_of efr)).
  Defined.
  
  Global Instance MapLike_EFrame {M : Type} `{MapLike M nat V} :
    MapLike (EFrame M) nat V := {}.
  - intros.
    simpl.
    eapply lookup_update_eq.
  - intros.
    simpl.
    eapply lookup_update_neq.
    assumption.
  Defined.
  
  Definition fp_of {T : Type} `{HasRange T} (x : T) := fst (dom x).
  Definition sp_of {T : Type} `{HasRange T} (x : T) := fst (dom x) + snd (dom x).
  Hint Unfold fp_of sp_of.
  
  Definition wf_EFrame {M : Type} `{MapLike M nat V} (efr : EFrame M) : Prop :=
    forall a, a ∈ efr -> efr ? a <> None.
  Hint Unfold wf_EFrame.
  
  Record PFrame (Var Arg Loc : Type) `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} :=
    {
      pvar_of : Var;
      parg_of : Arg;
      ploc_of : Loc;
    }.
  Hint Constructors PFrame.
  Global Arguments Build_PFrame { _ } { _ } { _ } { _ } { _ } { _ }.
  Global Arguments pvar_of { _ } { _ } { _ } { _ } { _ } { _ }.
  Global Arguments parg_of { _ } { _ } { _ } { _ } { _ } { _ }.
  Global Arguments ploc_of { _ } { _ } { _ } { _ } { _ } { _ }.

  Global Instance ReadableMapLike_PFrame {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} : ReadableMapLike (PFrame Var Arg Loc) string (A + SecTyV) := {}.
  - intros pfr x.
    eapply (pvar_of pfr ? x).
  - eapply (Build_PFrame ∅ ∅ ∅).
  - intros.
    simpl.
    eapply lookup_empty_map.
  Defined.

  Global Instance WriteableMapLike_PFrame {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} : WriteableMapLike (PFrame Var Arg Loc) string (A + SecTyV) := {}.
  intros x τℓ pfr.
  eapply (Build_PFrame (pvar_of pfr [x ↦ τℓ]) (parg_of pfr) (ploc_of pfr)).
  Defined.

  Global Instance MapLike_PFrame {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} : MapLike (PFrame Var Arg Loc) string (A + SecTyV) := {}.
  - intros.
    simpl.
    eapply lookup_update_eq.
  - intros.
    simpl.
    eapply lookup_update_neq.
    assumption.
  Defined.

  Global Instance FinMapLike_PFrame {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} : FinMapLike (PFrame Var Arg Loc) string (A + SecTyV) := {}.
  - intros pfr.
    eapply (values (pvar_of pfr)).
  - cbn.
    eapply values_empty.
  - intros.
    eapply values_add.
  Defined.
  
  Definition upd_loc {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} (x : string) (τ : SecTyV) (pfr : PFrame Var Arg Loc): PFrame Var Arg Loc.
    eapply (Build_PFrame (pvar_of pfr)
                         (parg_of pfr)
                         (update x τ (ploc_of pfr))).
  Defined.

  Definition upd_arg {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} (x : string) (τ : SecTyV) (pfr : PFrame Var Arg Loc): PFrame Var Arg Loc.
    eapply (Build_PFrame (pvar_of pfr)
                         (update x τ (parg_of pfr))
                         (ploc_of pfr)).
  Defined.
  
  Definition upd_var {Var Arg Loc : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} (x : string) (τℓ : A + SecTyV) (pfr : PFrame Var Arg Loc) : PFrame Var Arg Loc.
    eapply (Build_PFrame (update x τℓ (pvar_of pfr))
                         (parg_of pfr)
                         (ploc_of pfr)).
  Defined.
  Hint Unfold upd_loc upd_arg upd_var.

  Record Frame (Var Arg Loc Mem : Type) `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V} :=
    {
      pframe_of : PFrame Var Arg Loc;
      eframe_of : EFrame Mem
    }.
  Hint Constructors Frame.
  
  Global Arguments pframe_of { _ } { _ } { _ } { _ } { _ } { _ } { _ } { _ }.
  Global Arguments eframe_of { _ } { _ } { _ } { _ } { _ } { _ } { _ } { _ }.
  Global Arguments Build_Frame { _ } { _ } { _ } { _ } { _ } { _ } { _ } { _ }.

  Global Instance ReadableMapLike_nat_V_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V} : ReadableMapLike (Frame Var Arg Loc Mem) nat V := {}.
  - exact (fun fr n => eframe_of fr ? n).
  - eapply (Build_Frame ∅ ∅).
  - intros.
    simpl.
    eapply lookup_empty_map.
  Defined.

  Global Instance WriteableMapLike_nat_V_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: WriteableMapLike (Frame Var Arg Loc Mem) nat V := {}.
  exact (fun n v fr => Build_Frame (pframe_of fr) (eframe_of fr [n ↦ v])).
  Defined.
  
  Global Instance MapLike_nat_V_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: MapLike (Frame Var Arg Loc Mem) nat V := {}.
  Proof.
    - intros.
      simpl.
      eapply lookup_update_eq.
    - intros.
      simpl.
      eapply lookup_update_neq; assumption.
  Defined.
  Hint Resolve MapLike_nat_V_Fr.
  
  Global Instance HasVersion_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V} : HasVersion (Frame Var Arg Loc Mem).
  constructor.
  intros.
  eapply (version (eframe_of X)).
  Defined.
  Hint Resolve HasVersion_Fr.

  Global Instance ReadableMapLike_var_ty_or_sec_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: ReadableMapLike (Frame Var Arg Loc Mem) string (A + SecTyV) := {}.
  - exact (fun fr x => pframe_of fr ? x).
  - eapply (Build_Frame ∅ ∅).
  - intros.
    simpl.
    eapply lookup_empty_map.
  Defined.

  Global Instance WriteableMapLike_var_ty_or_sec_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: WriteableMapLike (Frame Var Arg Loc Mem) string (A + SecTyV) := {}.
  exact (fun x τℓ fr => Build_Frame (pframe_of fr [x ↦ τℓ]) (eframe_of fr)).
  Defined.  
  
  Global Instance MapLike_var_ty_or_sec_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: MapLike (Frame Var Arg Loc Mem) string (A + SecTyV) := {}.
  - intros.
    simpl.
    eapply lookup_update_eq.
  - intros.
    simpl.
    eapply lookup_update_neq; assumption.
  Defined.
  Hint Resolve MapLike_var_ty_or_sec_Fr.

  Global Instance FinMapLike_var_ty_or_sec_Fr {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: FinMapLike (Frame Var Arg Loc Mem) string (A + SecTyV) := {}.
  exact (fun fr => values (pframe_of fr)).
  - cbn.
    eapply values_empty.
  - intros.
    cbn.
    eapply values_add.
  Defined.
  Hint Resolve FinMapLike_var_ty_or_sec_Fr.

  Global Instance HasRange_Frame {Var Arg Loc Mem : Type} `{FinMapLike Var string (A + SecTyV)} `{FinMapLike Arg string SecTyV} `{FinMapLike Loc string SecTyV} `{MapLike Mem nat V}: HasRange (Frame Var Arg Loc Mem) := {}.
  intros fr.
  eapply (dom (eframe_of fr)).
  Defined.
  
End Frame.

Infix "∈" := in_range (at level 70).
Infix "∉" := (fun n r => not (in_range n r)) (at level 80).