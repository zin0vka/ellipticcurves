import Base: show, +, ==, parent, hash,*,-
using Primes
using Nemo
using Nemo: nmod
using AbstractAlgebra: Ring, RingElem

#y^2 = x^3 + ax +b
#Y^2Z = X^3 + aXZ^2 + bZ^3
mutable struct EllipticCurve{I <: RingElem}
  a::I
  b::I
end

#This is a projective point.
mutable struct Point{I<:RingElem}
  x::I
  y::I
  z::I
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

function z(p::Point{I}) where I
	return p.z
end

function x(p::PointOnCurve{I}) where I
	return x(point(p))
end

function y(p::PointOnCurve{I}) where I
	return y(point(p))
end

function z(p::PointOnCurve{I}) where I
	return z(point(p))
end

function infty(E::EllipticCurve{I}) where I<:RingElem
  return PointOnCurve(Point{I}(zero(parent(E)), one(parent(E)), zero(parent(E))), E)
end


function ==(E1::EllipticCurve{I}, E2::EllipticCurve{I}) where I
	return a(E1) == a(E2) && b(E1) == b(E2)
end

function ==(P::Point{I}, Q::Point{I}) where I<:RingElem
	ls = Union{Missing, I}[missing, missing, missing]
	Ps = [x(P), y(P), z(P)]
	Qs = [x(Q), y(Q), z(Q)]
	for k=1:3
		if !iszero(Ps[k]) && !iszero(Qs[k])
			ls[k] = Ps[k]*Qs[k]^(-1) #When this doesn't work, we have a factor.
		elseif iszero(Ps[k]) && iszero(Qs[k])
			ls[k] = missing
		else
			return false
		end
	end
	return isone(length(Set([l for l in ls if !ismissing(l)])))
end

function ==(P::PointOnCurve{I}, Q::PointOnCurve{I}) where I
	return curve(P) == curve(Q) && point(P) == point(Q)
end

function isinfty(p::PointOnCurve{I}) where I<:RingElem
	return p == infty(curve(p))
end

function a(E::EllipticCurve{I}) where I<:RingElem
  return E.a
end

function b(E::EllipticCurve{I}) where I<:RingElem
  return E.b
end

function disc(E::EllipticCurve{I}) where I<:RingElem
  return 4*a(E)^3+27*b(E)^2
end

#Y^2Z = X^3 + aXZ^2 + bZ^3
function ison(E::EllipticCurve{I},p::Point{I}) where I<:RingElem
  if parent(x(p)) == parent(a(E)) 
    return y(p)^2*z(p)-x(p)^3-a(E)*x(p)*z(p)^2-b(E)*z(p)^3 == zero(parent(a(E)))
  else
	return false
  end
end

function j(E::EllipticCurve{I}) where I<:RingElem
  A=a(E)
  B=b(E)
  return 1728*4*A^3*((4*A^3+27*B^2)^(-1))
end

function parent(E::EllipticCurve{I}) where I
	return parent(a(E))
end

function EllipticCurve(a::I,b::I) where  I<:RingElem
  parent(a) == parent(b) && return EllipticCurve{typeof(a)}(a,b)
end

function ==(E1::EllipticCurve{I}, E2::EllipticCurve{I}) where I
	return a(E1) == a(E2) && b(E1) == b(E2)
end

function hash(x::PointOnCurve{I}) where I #required for the dictionary to work properly
	return hash(string(x))
end

function negate(P::PointOnCurve{I}) where I <: RingElem
	return PointOnCurve(Point(x(P), -y(P), z(P)), curve(P))
end

function *(a::Int, P::PointOnCurve{I}) where I
	if a < 0
		return (-a)*negate(P)
	elseif a == 0
		return infty(curve(P))
	else
		return sum(fill(P,(a,1)))
	end
end

function double(P::PointOnCurve{I}) where I<:RingElem
	y(P) != 0 || return infty(curve(P))
	acoeff = a(curve(P))
	T = 3*x(P)^2 + acoeff*z(P)^2
	U = 2*y(P)*z(P)
	V = 2*U*x(P)*y(P)
	W = T^2 - 2*V
	X2 = U*W
	Y2 = T*(V-W) - 2*(U*y(P))^2
	Z2 = U^3
	return PointOnCurve(Point(X2,Y2,Z2), curve(P))
end

function +(P::PointOnCurve{I}, Q::PointOnCurve{I}) where I<:RingElem
	curve(P) == curve(Q) || throw("Adding points that aren't on the same curve. This is unadvised.")
	K = parent(curve(P))
	U1 = y(Q)*z(P)
	U2 = y(P)*z(Q)
	V1 = x(Q)*z(P)
	V2 = x(P)*z(Q)
	if V1 == V2
		if U1 != U2
			return infty(curve(P))
		else
			return double(P)
		end
	end
	U = U1 - U2
	V = V1 - V2
	W = z(P)*z(Q)
	A = U^2*W - V^3 - 2*V^2*V2
	X3 = V*A
	Y3 = U*(V^2*V2 - A) - V^3*U2
	Z3 = V^3*W
	return PointOnCurve(Point(X3,Y3,Z3),curve(P))
end

function -(P::PointOnCurve{I}, Q::PointOnCurve{I}) where I<:RingElem
	return P+(-1)*Q
end

function _points(E::EllipticCurve{I}) where I<:fq_nmod
	@warn "Brute-force generating points. This is not recommended. Please use Schoof's algorithm instead."
	K = parent(E)
	g = gen(K)
	z = zero(K)
	pts = PointOnCurve{elem_type(parent(E))}[]
	o = Int(order(K))
	for jx=0:o-1
		if ison(E, Point(z, g^jx, one(K)))
			push!(pts, PointOnCurve(Point(z, g^jx),E))
		end
	end
	for ix=0:o-1
		if ison(E, Point(g^ix, z, one(K)))
			push!(pts, PointOnCurve(Point(g^ix, z),E))
		end
	end
	for ix=0:o-1, jx=0:o-1
		if ison(E, Point(g^ix, g^jx, one(K)))
			push!(pts, PointOnCurve(Point(g^ix, g^jx,one(K)),E))
		end
	end
	return Set(pts)
end

function _points(E::EllipticCurve{I}) where I<:nmod
	@warn "Brute-force generating points. This is not recommended. Please use Schoof's algorithm instead."
	K = parent(E)
	g = one(K)
	z = zero(K)
	pts = PointOnCurve{elem_type(parent(E))}[]
	o = Int(order(K))
	for jx=0:o-1
		if ison(E, Point(z, jx*g, one(K)))
			push!(pts, PointOnCurve(Point(z, g^jx),E))
		end
	end
	for ix=0:o-1
		if ison(E, Point(ix*g, z, one(K)))
			push!(pts, PointOnCurve(Point(g^ix, z),E))
		end
	end
	for ix=0:o-1, jx=0:o-1
		if ison(E, Point(ix*g, jx*g, one(K)))
			push!(pts, PointOnCurve(Point(g^ix, g^jx,one(K)),E))
		end
	end
	return Set(pts)
end

function _amount_points(E::EllipticCurve{I}) where I<:RingElem
	return length(_points(E))+1
end

function random_point(E::EllipticCurve{I}) where I<:fq_nmod
	#Note that this function cannot generate (0,*) nor (*,0)
	K = parent(E)
	g = gen(K)
	o = Int(order(K))
	ix = rand(Int) % o
	jx = rand(Int) % o
	while !ison(E,Point(g^ix,g^jx,one(K)))
		ix = rand(Int) % o
		jx = rand(Int) % o
	end
	return PointOnCurve(Point(g^ix,g^jx,one(K)), E)
end

function random_point(E::EllipticCurve{I}) where I<:nmod
	K = parent(E)
	g = one(K)
	o = Int(order(K))
	ix = rand(Int) % o
	jx = rand(Int) % o
	while !ison(E,Point(ix*g,ix*g,one(K)))
		ix = rand(Int) % o
		jx = rand(Int) % o
	end
	return PointOnCurve(Point(g^ix,g^jx,one(K)), E)
end

#NOTE: This actually works weirdly quickly. Interesting. Maybe something to show at TWIL.
function ECM(N::Int, B::Int)
	(N > 0 && B > 0) || throw("Input positive integers!")
	R = ResidueRing(ZZ, N)
	a = rand(R)
	X = rand(R)
	Y = rand(R)
	b = Y^2 - X^3 - a*X
	E = EllipticCurve(a, b)
	P = PointOnCurve(Point(X, Y, one(R)), E)
	ps = primes(B)
	#This is inefficient, should instead perform multiplications in a loop
	e = prod([p^Int(floor(log(p, sqrt(N)))) for p in ps])
	Q = e*P
	qprime = gcd(Int(z(Q).data), N)
	return (Int(N/qprime), qprime)
end

K, X = FiniteField(7,2,"X")
P = Point(zero(K),one(K),zero(K))
Q = Point(zero(K),2*one(K),zero(K))

C = EllipticCurve(6*X+5, 6*X) #37 points, good for a toy example.
P = random_point(C)
Q = PointOnCurve(Point(x(P),-y(P),z(P)), C)
