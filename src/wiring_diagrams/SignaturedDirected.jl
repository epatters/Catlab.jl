""" Directed wiring diagrams over a symmetric monoidal signature.
"""
module SignaturedDirectedWiringDiagrams
export AbstractMonoidalSignature, MonoidalSignature

using ...Present, ...Theories, ...CategoricalAlgebra.CSets
using ..DirectedWiringDiagrams: TheoryWiringDiagram
import ...Present: add_generators!
import ...Theories: dom, codom

# Monoidal signatures
#####################

""" Schema for a (symmetric) monoidal signature.
"""
@present TheoryMonoidalSignature(FreeSchema) begin
  (Ob, Hom, InOb, OutOb)::Ob
  in_ob::Hom(InOb, Ob)
  in_hom::Hom(InOb, Hom)
  out_ob::Hom(OutOb, Ob)
  out_hom::Hom(OutOb, Hom)
end

@present TheoryNamedMonoidalSignature <: TheoryMonoidalSignature begin
  Name::Data
  ob_name::Attr(Ob, Name)
  hom_name::Attr(Hom, Name)
end

const AbstractMonoidalSignature = AbstractACSetType(TheoryMonoidalSignature)

""" Signature for a (symmetric) monoidal category.

A monoidal signature specifies the generating objects and morphisms of an SMC.
Monoidal signatures are isomorphic to whole-grain Petri nets.
"""
const MonoidalSignature = ACSetType(TheoryNamedMonoidalSignature,
                                    index=[:in_ob,:in_hom,:out_ob,:out_hom])

function (::Type{Sig})(pres::Presentation; kw...) where Sig <: AbstractMonoidalSignature
  sig = Sig()
  add_generators!(sig, pres; kw...)
  sig
end

MonoidalSignature(pres::Presentation{T,Name}) where {T,Name} =
  MonoidalSignature{Name}(pres)

dom(sig::AbstractMonoidalSignature, hom) =
  subpart(sig, incident(sig, hom, :in_hom), :in_ob)
codom(sig::AbstractMonoidalSignature, hom) =
  subpart(sig, incident(sig, hom, :out_hom), :out_ob)

""" Add generators from presentation of SMC to monoidal signature.
"""
function add_generators!(sig::AbstractMonoidalSignature, pres::Presentation;
                         ob_name=first, hom_name=first)
  # Add object generators from presentation.
  obs = generators(pres, :Ob)
  ob_ids = add_parts!(sig, :Ob, length(obs))
  if has_subpart(sig, :ob_name)
    sig[ob_ids, :ob_name] = map(ob_name, obs)
  end

  # Add morphism generators from presentation.
  homs = generators(pres, :Hom)
  hom_ids = add_parts!(sig, :Hom, length(homs))
  if has_subpart(sig, :hom_name)
    sig[hom_ids, :hom_name] = map(hom_name, homs)
  end
  ob_id = x -> ob_ids[generator_index(pres, first(x))]
  for (i, f) in zip(hom_ids, homs)
    in_obs = map(ob_id, collect(dom(f)))
    out_obs = map(ob_id, collect(codom(f)))
    add_parts!(sig, :InOb, length(in_obs), in_ob=in_obs, in_hom=i)
    add_parts!(sig, :OutOb, length(out_obs), out_ob=out_obs, out_hom=i)
  end
end

# Signatured wiring diagrams
############################

@present TheorySignaturedWiringDiagram <: TheoryWiringDiagram begin
  # FIXME: Should also extend schema for monoidal signature.
  (Ob, Hom, InOb, OutOb)::Ob
  in_ob::Hom(InOb, Ob)
  in_hom::Hom(InOb, Hom)
  out_ob::Hom(OutOb, Ob)
  out_hom::Hom(OutOb, Hom)

  box_proj::Hom(Box, Hom)
  in_proj::Hom(InPort, InOb)
  out_proj::Hom(OutPort, OutOb)
  outer_in_ob::Hom(OuterInPort, Ob)
  outer_out_ob::Hom(OuterOutPort, Ob)

  compose(src, out_proj, out_ob) == compose(tgt, in_proj, in_ob)
  compose(in_src, outer_in_ob) == compose(in_tgt, in_proj, in_ob)
  compose(out_src, out_proj, out_ob) == compose(out_tgt, outer_out_ob)
  compose(pass_src, outer_in_ob) == compose(pass_tgt, outer_out_ob)
end


end
