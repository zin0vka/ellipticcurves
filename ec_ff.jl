import Base: show, +, ==, parent, hash,*
using Nemo
using AbstractAlgebra: Field, FieldElem

mutable struct EllipticCurve{I <: FieldElem}
  a::I
  b::I
end

#we also use this for creation
mutable struct Point{I}
  x::Union{I,Missing}
  y::Union{I,Missing}
end

mutable struct PointOnCurve{I}
   p::Point{I}
   E::EllipticCurve{I}
end

function curve(p::PointOnCurve{I}) where I
	return p.E
end

function point(p::PointOnCurve{I}) where I
	return p.p
end

function x(p::Point{I}) where I
	return p.x
end

function y(p::Point{I}) where I
	return p.y
end

function x(p::PointOnCurve{I}) where I
	return x(point(p))
end

function y(p::PointOnCurve{I}) where I
	return y(point(p))
end

function infty(E::EllipticCurve{I}) where I<:FieldElem
  return PointOnCurve(Point{I}(missing,missing), E)
end

function isinfty(p::Point{I}) where I<:FieldElem
  return ismissing(x(p)) && ismissing(y(p))
end

function isinfty(p::PointOnCurve{I}) where I<:FieldElem
	return isinfty(point(p))
end

function show(io::IO, a::Point{I}) where I<:FieldElem
  if isinfty(a)
    println(io, "∞")
  else
    println(io, "($(x(a)),$(y(a)))")
  end
end

function show(io::IO, a::PointOnCurve{I}) where I<:FieldElem
	println(io, "$(point(a))  on  $(curve(a))")
end

function ison(E::EllipticCurve{I},p::Point{I}) where I<:FieldElem
  if isinfty(p)
    return true
  elseif !isinfty(p) && parent(x(p)) == parent(a(E)) 
    return y(p)^2-x(p)^3-a(E)*x(p)-b(E) == zero(parent(a(E)))
  end
end

function a(E::EllipticCurve{I}) where I<:FieldElem
  return E.a
end

function b(E::EllipticCurve{I}) where I<:FieldElem
  return E.b
end

function disc(E::EllipticCurve{I}) where I<:FieldElem
  return 4*a(E)^3+27*b(E)^2
end

function j(E::EllipticCurve{I}) where I<:FieldElem
  A=a(E)
  B=b(E)
  return 1728*4*A^3*((4*A^3+27*B^2)^(-1))
end

function _points(E::EllipticCurve{I}) where I<:FieldElem
	@warn "Brute-force generating points. This is not recommended. Please use Schoof's algorithm instead."
	K = parent(E)
	typeof(K) == FqNmodFiniteField || throw("Generating points on a curve not defined over a finite field.")
	g = gen(K)
	z = zero(parent(E))
	pts = PointOnCurve{elem_type(parent(E))}[]
	o = Int(order(K))
	for jx=0:o-1
		if ison(E, Point(z, g^jx))
			push!(pts, PointOnCurve(Point(z, g^jx),E))
		end
	end
	for ix=0:o-1
		if ison(E, Point(g^ix, z))
			push!(pts, PointOnCurve(Point(g^ix, z),E))
		end
	end
	for ix=0:o-1, jx=0:o-1
		if ison(E, Point(g^ix, g^jx))
			push!(pts, PointOnCurve(Point(g^ix, g^jx),E))
		end
	end
	return Set(pts)
end

function EllipticCurve(a::I,b::I) where  I<:FieldElem
  parent(a) == parent(b) && return EllipticCurve{typeof(a)}(a,b)
end

function parent(E::EllipticCurve{I}) where I
	return parent(a(E))
end

function ==(P::Point{I}, Q::Point{I}) where I
	if isinfty(P) || isinfty(Q)
		return isinfty(P) && isinfty(Q)
	else
		return x(P) == x(Q) && y(P) == y(Q)
	end
end

function ==(E1::EllipticCurve{I}, E2::EllipticCurve{I}) where I
	return a(E1) == a(E2) && b(E1) == b(E2)
end

function ==(P::PointOnCurve{I}, Q::PointOnCurve{I}) where I
	return curve(P) == curve(Q) && point(P) == point(Q)
end

function hash(x::PointOnCurve{I}) where I #required for the dictionary to work properly
	return hash(string(x))
end

function *(a::Int, P::PointOnCurve{I}) where I
	a >= 0 || throw("Not implemented yet.")
	if a == 0
		return infty(curve(P))
	else
		return sum(fill(P,(a,1)))
	end
end

function +(P::PointOnCurve{I}, Q::PointOnCurve{I}) where I<:FieldElem
	curve(P) == curve(Q) || throw("Adding points that aren't on the same curve.")
	if isinfty(P)
		return Q
	elseif isinfty(Q)
		return P
	elseif x(P) == x(Q) && y(P) == -y(Q)
		return infty(curve(P))
	else
		l = zero(parent(curve(P)))
		if P != Q
			l = (x(Q)-x(P))^(-1)*(y(Q)-y(P))
		else
			l = (2*y(P))^(-1)*(3*x(P)^2+a(curve(P)))
		end
		x3 = l^2 - x(P) - x(Q)
		y3 = -l*x3 - y(P) + l*x(P)
		return PointOnCurve(Point(x3, y3), curve(P))
	end
end

function _amount_points(E::EllipticCurve{I}) where I<:FinFieldElem
	return length(_points(E))+1
end

function random_point(E::EllipticCurve{I}) where I<:FinFieldElem
	#Note that this function cannot generate (0,*) nor (*,0)
	K = parent(E)
	g = gen(K)
	o = Int(order(K))
	ix = rand(Int) % o
	jx = rand(Int) % o
	while !ison(E,Point(g^ix,g^jx))
		ix = rand(Int) % o
		jx = rand(Int) % o
	end
	return PointOnCurve(Point(g^ix,g^jx), E)
end

#ECDH_send assumes prime order and secret in ]0, o[ where o is the order of the elliptic curve.
function ECDH_send(a::Int, G::PointOnCurve{I}) where I
	return a*G
end

function ECDH_recv(a::Int, B::PointOnCurve{I}) where I
	return a*B
end

function ECM(N::Int, B::Int)
	(N>0 && B>0) || throw("Input positive integers.")
	a = rand(Int) % N
	X = rand(Int) % N
	Y = rand(Int) % N
end

K,X = FiniteField(7,2,"X")
C = EllipticCurve(X,X+1) #This curve has 40 points on it. Thought it was a bad choice at first, but it is actually pretty nice, since it still is cyclic.
j(C)
disc(C)

#dumb test cases to make sure that the hash now works correctly.
pt = PointOnCurve(Point(X+3,5*X),C)
pt2 = pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt+pt #Oh yes, isn't it lovely~~~

C2 = EllipticCurve(6*X+5, 6*X) #37 points, good for a toy example.

g = random_point(C2)
a_secret = 5
println("Alice's secret: $a_secret")
A = ECDH_send(a_secret, g)
println("Public data: $A")
b_secret = 7
println("Bob's secret: $b_secret")
B = ECDH_send(b_secret, g)
println("Public data: $B")
println("Alice receives common secret")
println(ECDH_recv(a_secret, B))
println("Bob receives common secret")
println(ECDH_recv(b_secret, A))
