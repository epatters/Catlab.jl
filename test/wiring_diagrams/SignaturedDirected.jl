module TestSignaturedDirectedWiringDiagrams
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra.CSets
using Catlab.WiringDiagrams

# Monoidal signatures
#####################

@present SigMonoid(FreeSymmetricMonoidalCategory) begin
  X::Ob
  m::Hom(X⊗X, X)
  e::Hom(munit(), X)
end

sig = MonoidalSignature(SigMonoid)
@test (nparts(sig, :Ob), nparts(sig, :Hom)) == (1,2)
@test sig[:ob_name] == [:X]
@test sig[:hom_name] == [:m, :e]
@test dom(sig, 1) == [1,1]
@test codom(sig, 1) == [1]

@present SigModuleOverRig(FreeSymmetricMonoidalCategory) begin
  R::Ob
  times::Hom(R⊗R, R)
  one::Hom(munit(), R)
  plus::Hom(R⊗R, R)
  zero::Hom(munit(), R)

  X::Ob
  mplus::Hom(X⊗X, X)
  mzero::Hom(munit(), X)
  scalar::Hom(R⊗X, X)
end

sig = MonoidalSignature(SigModuleOverRig)
@test (nparts(sig, :Ob), nparts(sig, :Hom)) == (2,7)
@test sig[:ob_name] == [:R,:X]
scalar = only(incident(sig, :scalar, :hom_name))
@test dom(sig, scalar) == [1,2]
@test codom(sig, scalar) == [2]

end
