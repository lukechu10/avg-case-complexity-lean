import AverageCaseComplexity.Completeness.TupleEncoding

open AverageCaseComplexity AverageCaseComplexity.Completeness.TwoQuery

def testSeed : Seed := ⟨[true], [false, true], [false, false], false, [], [true, false]⟩
def testInstance : Instance := ⟨[true], [false, true], 3, true, [], 2⟩

example : decodeSeed (encodeSeed testSeed) = some testSeed := decodeSeed_encodeSeed _
example : decode (encode testInstance) = some testInstance := decode_encode _
example (n : ℕ) : decodeSeed (List.replicate n true) = none := decodeSeed_ones n
example : decode [] = none := by decide

example (u v : Instance) (h : encode u = encode v) : u = v := encode_injective h
example (w : Word) (z : Instance) (h : decode w = some z) : encode z = w :=
  decode_sound w z h

-- Parsing cannot silently accept a noncanonical spelling of a seed.
example (w : Word) (z : Seed) (h : decodeSeed w = some z) : encodeSeed z = w :=
  decodeSeed_encodeSeed_eq w z h

#print axioms decodeSeed_encodeSeed
#print axioms decodeSeed_encodeSeed_eq
#print axioms decode_encode
#print axioms encodeSeed_length_le
#print axioms payload_length_le_encode_length
