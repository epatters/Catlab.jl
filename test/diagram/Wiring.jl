module TestWiring

using Base.Test
using Catlab.Doctrine
using Catlab.Diagram

# For testing purposes, check equality of port symbols.
function Wiring.validate_ports(source_port::Symbol, target_port::Symbol)
  if source_port != target_port
    throw(PortValueError(source_port, target_port))
  end
end

# Low-level graph interface
###########################

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
f = Hom(:f, A, B)
g = Hom(:g, B, C)
h = Hom(:h, C, D)

# Operations on boxes
d = WiringDiagram(A, C)
@test nboxes(d) == 0
@test_throws NullException box(d,input_id(d))
@test_throws NullException box(d,output_id(d))

fv = add_box!(d, f)
@test nboxes(d) == 1
@test box(d, fv).value == :f
@test box(d, fv) == Box(f)
rem_box!(d, fv)
@test nboxes(d) == 0

fv = add_box!(d, f)
gv = add_box!(d, g)
hv = add_box!(d, h)
@test nboxes(d) == 3
@test [b.value for b in boxes(d)] == [:f,:g,:h]
@test boxes(d) == [Box(f),Box(g),Box(h)]
rem_boxes!(d, [fv,hv])
@test nboxes(d) == 1
@test boxes(d) == [Box(g)]

# Operations on wires
d = WiringDiagram(A, C)
fv = add_box!(d, f)
gv = add_box!(d, g)

@test port_value(d, Port(input_id(d),OutputPort,1)) == :A
@test port_value(d, Port(output_id(d),InputPort,1)) == :C
@test port_value(d, Port(fv,InputPort,1)) == :A
@test port_value(d, Port(fv,OutputPort,1)) == :B

@test nwires(d) == 0
@test !has_wire(d, fv, gv)
@test !has_wire(d, (fv,1) => (gv,1))
add_wire!(d, (input_id(d),1) => (fv,1))
add_wire!(d, (fv,1) => (gv,1))
add_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d) == 3
@test has_wire(d, fv, gv)
@test has_wire(d, (fv,1) => (gv,1))
@test_throws PortValueError add_wire!(d, (gv,1) => (fv,1))
@test wires(d) == map(Wire, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(d),1),
])

# Graph properties.
@test Set(all_neighbors(d, fv)) == Set([input_id(d),gv])
@test Set(all_neighbors(d, gv)) == Set([fv,output_id(d)])
@test neighbors(d, fv) == [gv]
@test out_neighbors(d, fv) == [gv]
@test in_neighbors(d, gv) == [fv]
@test wires(d, input_id(d)) == [ Wire((input_id(d),1) => (fv,1)) ]
@test wires(d, fv) == map(Wire, [
  ((input_id(d),1) => (fv,1)),
  ((fv,1) => (gv,1))
])
@test out_wires(d, fv) == [ Wire((fv,1) => (gv,1)) ]
@test out_wires(d, Port(fv,OutputPort,1)) == [ Wire((fv,1) => (gv,1)) ]
@test in_wires(d, gv) == [ Wire((fv,1) => (gv,1)) ]
@test in_wires(d, Port(gv,InputPort,1)) == [ Wire((fv,1) => (gv,1)) ]

rem_wires!(d, fv, gv)
@test nwires(d) == 2
@test !has_wire(d, fv, gv)
rem_wire!(d, (input_id(d),1) => (fv,1))
@test wires(d) == [ Wire((gv,1) => (output_id(d),1)) ]

# Substitution
f, g, h = Hom(:f,A,B), Hom(:g,B,C), Hom(:h,C,D)
sub = WiringDiagram(B,D)
gv = add_box!(sub, g)
hv = add_box!(sub, h)
add_wires!(sub, Pair[
  (input_id(sub),1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(sub),1),
])
d = WiringDiagram(A,D)
fv = add_box!(d, f)
subv = add_box!(d, sub)
add_wires!(d, Pair[
  (input_id(d),1) => (fv,1),
  (fv,1) => (subv,1),
  (subv,1) => (output_id(d),1),
])
@test boxes(d) == [ Box(f), sub ]
@test boxes(sub) == [ Box(g), Box(h) ]
substitute!(d, subv)
@test nboxes(d) == 3
@test Set(boxes(d)) == Set([ Box(f), Box(g), Box(h) ])
box_map = Dict(box(d,v).value => v for v in box_ids(d))
@test nwires(d) == 4
@test Set(wires(d)) == Set(map(Wire, [
  (input_id(d),1) => (box_map[:f],1),
  (box_map[:f],1) => (box_map[:g],1),
  (box_map[:g],1) => (box_map[:h],1),
  (box_map[:h],1) => (output_id(d),1),
]))

d = WiringDiagram(A,D)
fv = add_box!(d, f)
gv = add_box!(d, g)
hv = add_box!(d, h)
add_wires!(d, Pair[
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(d),1)
])
encapsulate!(d, [fv,gv])
@test nboxes(d) == 2
sub = first((b for b in boxes(d) if isa(b, WiringDiagram)))
@test nboxes(sub) == 2
@test boxes(sub) == [ Box(f), Box(g) ]
box_map = Dict(box(sub,v).value => v for v in box_ids(sub))
@test wires(sub) == map(Wire, [
  (input_id(sub),1) => (box_map[:f],1),
  (box_map[:f],1) => (box_map[:g],1),
  (box_map[:g],1) => (output_id(sub),1),
])

# High-level categorical interface
##################################

# Category
#---------

# Generators
f = WiringDiagram(Hom(:f,A,B))
g = WiringDiagram(Hom(:g,B,A))
@test nboxes(f) == 1
@test boxes(f) == [ Box(Hom(:f,A,B)) ]
@test nwires(f) == 2
@test Ports([:A]) == Ports([:A])
@test WiringDiagram(Hom(:f,A,B)) == WiringDiagram(Hom(:f,A,B))

# Composition
@test nboxes(compose(f,g)) == 2
@test boxes(compose(f,g)) == [ Box(Hom(:f,A,B)), Box(Hom(:g,B,A)) ]
@test nwires(compose(f,g)) == 3

# Domains and codomains
@test dom(f) == Ports([:A])
@test codom(f) == Ports([:B])
@test dom(compose(f,g)) == Ports([:A])
@test codom(compose(f,g)) == Ports([:A])
@test_throws Exception compose(f,f)

# Associativity
@test compose(compose(f,g),f) == compose(f,compose(g,f))

# Identity
@test compose(id(dom(f)), f) == f
@test compose(f, id(codom(f))) == f

# Symmetric monoidal category
#----------------------------

# Domains and codomains
@test dom(otimes(f,g)) == otimes(dom(f),dom(g))
@test codom(otimes(f,g)) == otimes(codom(f),codom(g))

# Associativity and unit
X, Y = Ports([:A,:B]), Ports([:C,:D])
I = munit(Ports)
@test otimes(X,I) == X
@test otimes(I,X) == X
@test otimes(otimes(X,Y),X) == otimes(X,otimes(Y,X))
@test otimes(otimes(f,g),f) == otimes(f,otimes(g,f))

# Braiding
@test compose(braid(X,Y),braid(Y,X)) == id(otimes(X,Y))

# Permutations
W = otimes(X,Y)
@test permute(W, [1,2,3,4]) == id(W)
@test permute(W, [1,2,3,4], inverse=true) == id(W)
@test permute(W, [3,4,1,2]) == braid(X,Y)
@test permute(W, [3,4,1,2], inverse=true) == braid(Y,X)
@test_throws AssertionError permute(W, [1,2])

# Diagonals
#----------

# Basic composition
d = WiringDiagram(dom(f), otimes(codom(f),codom(f)))
fv1 = add_box!(d, first(boxes(f)))
fv2 = add_box!(d, first(boxes(f)))
add_wires!(d, [
  (input_id(d),1) => (fv1,1),
  (input_id(d),1) => (fv2,1),
  (fv1,1) => (output_id(d),1),
  (fv2,1) => (output_id(d),2),
])
@test compose(mcopy(dom(f)), otimes(f,f)) == d

# Domains and codomains
@test dom(mcopy(Ports([:A]))) == Ports([:A])
@test codom(mcopy(Ports([:A]))) == Ports([:A,:A])
@test dom(mcopy(Ports([:A,:B]),3)) == Ports([:A,:B])
@test codom(mcopy(Ports([:A,:B]),3)) == Ports([:A,:B,:A,:B,:A,:B])

# Associativity
X = Ports([:A])
@test compose(mcopy(X), otimes(id(X),mcopy(X))) == mcopy(X,3)
@test compose(mcopy(X), otimes(mcopy(X),id(X))) == mcopy(X,3)

# Commutativity
@test compose(mcopy(X), braid(X,X)) == mcopy(X)

# Unit
@test compose(mcopy(X), otimes(id(X),delete(X))) == id(X)

# Codiagonals
#------------

# Domains and codomains
@test dom(mmerge(Ports([:A]))) == Ports([:A,:A])
@test codom(mmerge(Ports([:A]))) == Ports([:A])
@test dom(mmerge(Ports([:A,:B]),3)) == Ports([:A,:B,:A,:B,:A,:B])
@test codom(mmerge(Ports([:A,:B]),3)) == Ports([:A,:B])

# Associativity
X = Ports([:A])
@test compose(otimes(id(X),mmerge(X)), mmerge(X)) == mmerge(X,3)
@test compose(otimes(mmerge(X),id(X)), mmerge(X)) == mmerge(X,3)

# Commutativity
@test compose(braid(X,X), mmerge(X)) == mmerge(X)

# Unit
@test compose(otimes(id(X),create(X)), mmerge(X)) == id(X)

# Expression conversion
#----------------------

# Functorality
f, g = Hom(:f,A,B), Hom(:g,B,A)
fd, gd = WiringDiagram(f), WiringDiagram(g)
@test to_wiring_diagram(f) == fd
@test to_wiring_diagram(compose(f,g)) == compose(fd,gd)
@test to_wiring_diagram(otimes(f,g)) == otimes(fd,gd)
@test to_wiring_diagram(munit(FreeSymmetricMonoidalCategory.Ob)) == munit(Ports)

end
