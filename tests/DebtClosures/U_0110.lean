import Uwueave.FiniteSummaryCodec

open Uwueave
open Uwueave.FiniteSummaryCodec

universe u v

theorem debtClosure_U_0110 :
    (forall {S : Type u} {R : Type v} [MergeState S] [BEq R] [LawfulBEq R]
      (complete : CompleteSpec S R),
      Function.Injective (decodeKey complete) /\
        Function.Surjective (decodeKey complete)) /\
    (forall {S : Type u} {R : Type v} [MergeState S] [BEq R] [LawfulBEq R]
      (complete : CompleteSpec S R) (key : ClassKey complete),
      decodeKey complete (encodeKey complete key) = key) /\
    (forall {S : Type u} {R : Type v} [MergeState S] [BEq R] [LawfulBEq R]
      (complete : CompleteSpec S R) (index : ClassIndex complete),
      encodeKey complete (decodeKey complete index) = index) /\
    (forall {S : Type u} {R : Type v} [MergeState S] [BEq R] [LawfulBEq R]
      (complete : CompleteSpec S R) (bits : Nat)
      (code : ClassIndex complete -> Fin (2 ^ bits)),
      Function.Injective code -> classCount complete <= 2 ^ bits) /\
    classCount Fixtures.membership = 2 /\
    classCount Fixtures.thresholdTwo = 5 := by
  exact
    ⟨fun complete => class_count_exact complete,
      fun complete key => decode_encode_key complete key,
      fun complete index => encode_decode_index complete index,
      fun complete bits code hinjective =>
        fixedWidth_information_lower_bound complete bits code hinjective,
      Fixtures.membership_two_classes,
      Fixtures.thresholdTwo_five_classes⟩
