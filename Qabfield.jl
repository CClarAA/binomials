###############################################################################
#
#   Implementation of QabField
#   Functions so that we can use Qab as coefficient field
#
###############################################################################

type QabField <: Nemo.Field # union of cyclotomic fields
end

function Base.show(io::IO, a::QabField)
  println(io, "Abelian closure of Q")
end

type QabElem <: Nemo.FieldElem
  data::nf_elem  #actually in cyclotomic field
  c::Int #conductor of field
end

function Base.show(io::IO, a::QabElem)
  println(io, a.data, " in Q(z_$(a.c))")
end

function is_conductor(n::Int)
  if isodd(n) 
    return true
  end
  return n % 4 == 0
end

function cyclotomic_field(n::Int)
  Zx, x = FlintZZ["x"]
  return number_field(cyclotomic(n, x), "z_$n")
end

function coerce_up(K::AnticNumberField, n::Int, a::QabElem)
  d = div(n, a.c)
  @assert n % a.c == 0
  #z_n^(d) = z_a
  Qx, x = FlintQQ["x"]
  return QabElem(evaluate(Qx(a.data), gen(K)^d), n)
end

function coerce_down(K::AnticNumberField, n::Int, a::QabElem)
  error("missing")
end

function make_compatible(a::QabElem, b::QabElem)
  if a.c == b.c
    return a,b
  end
  d = lcm(a.c, b.c)
  K, z = cyclotomic_field(d)
  return coerce_up(K, d, a), coerce_up(K, d, b)
end

function root_of_unity(K::QabField, n::Int)
  if n % 2 == 0 && n % 4 != 0
    c = div(n, 2)
  else
    c = n
  end
  K, z = cyclotomic_field(c)
  if c == n
    return QabElem(z, c)
  else
    return QabElem(-z, c)
  end
end

import Base.+, Base.*, Base.-, Base.//, Base.==, Base.zero, Base.one, Base.^
import Nemo.mul!, Nemo.addeq!, Nemo.divexact, Nemo.iszero

function ^(a::QabElem, n::Integer)
  return QabElem(a.data^n, a.c)
end

function ^(a::QabElem, n::fmpz)
  return a^Int(n)
end

function +(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return QabElem(a.data+b.data, a.c)
end

function addeq!(c::QabElem, a::QabElem)
	c, a=make_compatible(c, a)
	addeq!(c.data, a.data)
	return c
end

function -(a::QabElem)
  return QabElem(-a.data,a.c)
end

function neg!(a::QabElem)
	mul!(a.data,a.data,-1)
	return a
end

function *(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return QabElem(a.data*b.data, a.c)
end

*(a::Integer, b::QabElem) = QabElem(b.data*a, b.c)
*(a::fmpz, b::QabElem) = QabElem(b.data*a, b.c)

function mul!(c::QabElem, a::QabElem, b::QabElem)
	a, b = make_compatible(a, b)
	b, c = make_compatible(b, c)
  a, b = make_compatible(a, b)
	mul!(c.data, a.data, b.data)
	return c
end

function -(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return QabElem(a.data-b.data, a.c)
end

function //(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return QabElem(a.data//b.data, a.c)
end  

# // with other name
function div(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return QabElem(a.data//b.data, a.c)
end  

function divexact(a::QabElem, b::QabElem)
	a, b = make_compatible(a, b)
  return QabElem(divexact(a.data,b.data), a.c)
end

function inv(a::QabElem)
	return(Base.one(Base.parent(a))//a)
end

function isone(a::QabElem)
	return(isone(a.data))
end

function iszero(a::QabElem)
	return(iszero(a.data))
end

function ==(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return a.data==b.data
end  

function ==(a::QabElem, b::Integer)
	c = Base.parent(a)(b)
	a, c = make_compatible(a,c)
	return a==c
end

function (b::QabField)(a::Integer)
  return a*root_of_unity(b, 1)
end

function Base.copy(a::QabElem)
  return QabElem(a.data, a.c)
end

# deepcopy is the same as copy
function deepcopy(a::QabElem, b::QabElem)
  a, b = make_compatible(a, b)
  return QabElem(a.data//b.data, a.c)
end  

Base.parent(::QabElem) = QabField()
Base.one(::QabField) = QabField()(1)
Base.one(::QabElem) = QabField()(1)


###############################################################################
#
#   Partial character functions
#
###############################################################################

type PChar
	#A has generators of the lattice in rows
  A::fmpz_mat
	#images of the generators are saved in b
  b::Array{FieldElem, 1}
	#Delta are the indices of the cellular variables of the associated ideal  
	#(the partial character is a partial character on Z^Delta)
  D::Set{Int64}
end

function (Chi::PChar)(b::fmpz_mat)
  @assert rows(b)==1
  @assert cols(b) == cols(Chi.A)
  s = solve(Chi.A', b')
  return evaluate(FacElem(Dict([(Chi.b[i], s[i, 1]) for i=1:length(Chi.b)])))
end

function (Chi::PChar)(b::Array{Nemo.fmpz,})
	@assert size(b,2)==cols(Chi.A)
	B=Matrix(FlintZZ,1,cols(Chi.A),b)
	s = solve(Chi.A', B')
	return evaluate(FacElem(Dict([(Chi.b[i], s[i, 1]) for i=1:length(Chi.b)])))
end

function isroot_of_unity(a::QabElem)
  b = a^a.c
  return b.data == 1 || b.data == -1
end

function Hecke.isone(a::QabElem)
  return isone(a.data)
end

function LatticeEqual(A::fmpz_mat,B::fmpz_mat)
  #lattices are always given as basis vectors, so if they are equal they must have the same 
  #number of generators
  @assert rows(A)==rows(B)  
  @assert cols(A)==cols(B)
  A=A'
  B=B'

  #use solve to check if lattices are equal
  testVector=Matrix(FlintZZ,rows(A),1,[0; 0; 0])

  #test if A contained in B
  for k=1:cols(A)
	for j=1:rows(A)
	testVector[j,1]=A[j,k]
	end
	if cansolve(B,testVector)[1]==false
          return(false)
	end
  end	
  for k=1:cols(A)
	for j=1:rows(A)
	testVector[j,1]=B[j,k]
	end
	if cansolve(A,testVector)[1]==false
          return(false)
	end
  end	
  return(true)
end

function Hecke.order(a::QabElem)
  f = factor(fmpz(2*a.c))
  o = 1
  for (p, e) = f.fac
    b = a^div(2*a.c, Int(p)^e)
    f = 0

    while !isone(b)
      b = b^p
      f += 1
    end
    o *= p^f
  end
  return o
end

function PCharEqual(P::PChar,Q::PChar)
  if LatticeEqual(P.A,Q.A)==false
		return(false)
  end
  if (P.b==Q.b)==false
		return(false)
  end
	if (P.D==Q.b)==false
		return(false)
	end
  return(true)
end

function Hecke.root(a::QabElem, n::Int)
 o = order(a)
 l = o*n
 mu = root_of_unity(QabField(), Int(l))
 return mu
end

function allroot(a::QabElem, n::Int)
  o = order(a)
  l = o*n
  mu = root_of_unity(QabField(), Int(l))
  A=[mu]
  for k=1:(l-1)
    A=[A mu^(k+1)]
  end
  return A
end

function Hecke.saturate(L::PChar)
  H = hnf(L.A')
  s = sub(H, 1:cols(H), 1:cols(H))
  i, d = pseudo_inv(s)  #is = d I_n
  #so, saturation is i' * H // d
  S = divexact(i'*L.A, d)
  l = QabElem[]
  for k=1:rows(s)
    c = i[1,k]
    for j=2:cols(s)
      c = gcd(c, i[j,k])
      if isone(c)
        break
      end
    end
    mu = evaluate(FacElem(Dict([(L.b[j], div(i[j, k], c)) for j=1:cols(s)])))
    mu = root(mu, Int(div(d, c)))
    push!(l,  mu)  # for all saturations, use all roots - a cartesian product
  end
  #new values are d-th root of l
  return PChar(S, l, L.D)
end

Hecke.elem_type(::QabField) = QabElem

function minimise!(a::QabElem)
  su = [i for i=0:degree(parent(a.data))-1 if coeff(a.data, i) != 1]
  if length(su) == 1 # we have a root of unity - definitely.
  end
  if a.c < 3
    return a
  end
  ln = factor(fmpz(a.c))
  for (p,e) = ln.fac
    n2 = Int(p)^e
    n1 = div(a.c, n2)
    C, z_n1 = cyclotomic_field(n1)
    Ct, t = PolynomialRing(C)
    D, z_n2 = cyclotomic_field(n2)
    L = zero(Ct)

    g, e, f = gcdx(n1, n2)
    @assert g == 1
    z_n1 = z_n1^f
    z_n2 = z_n2^e
    #so z_c = z_n1^f z_n2^e = (z_c^n2)^f (z_c^n1)^e
    for i=0:degree(parent(a.data))-1
      c = coeff(a.data, i)
      x = z_n2^i
      for j=0:degree(parent(x))-1
        L += t^j*c*coeff(x, j)*z_n1^i
      end
    end
#    println("$p: $(a.data) -> $L")
    #if the index of all non-zero coefficients is divisible by p^?, then we can
    #move down some levels
    g = gcd([i for i=0:degree(L) if coeff(L, i) != 0])
    g = gcd(g, n2)  
    if g > 1
      m = div(a.c, g)
      E, z_m = cyclotomic_field(m)
      Qt = parent(E.pol)
      zn1 = z_m^div(m, n1)
      zn2 = z_m^div(m, div(n2, g))
      mu = sum([Qt(coeff(L, g*i))(zn1)*zn2^i for i=0:div(degree(L), g)])
      a.data = mu
      a.c = m
      return minimise!(a)
    end
  end
  return a
end


#achtung um das zu benutzen muss man using IterTools davor eingeben!
function PCharSaturateAll(L::PChar)
  H = hnf(L.A')
  s = sub(H, 1:cols(H), 1:cols(H))
  i, d = pseudo_inv(s)  #is = d I_n
  #so, saturation is i' * H // d
  S = divexact(i'*L.A, d)
  Re = QabElem[]
 
  B = Array[]
  for k=1:rows(s)
    c = i[1,k]
    for j=2:cols(s)
      c = gcd(c, i[j,k])
      if isone(c)
        break
      end
    end
    mu = evaluate(FacElem(Dict([(L.b[j], div(i[j, k], c)) for j=1:cols(s)])))
    mu = allroot(mu, Int(div(d, c)))
    push!(B,  mu) 
  end
  
  C=IterTools.product(B)
  T=Array[]
  for a in C
		push!(T,collect(a))
  end
  
  Result=PChar[]
  for k=1:size(T,1)
			push!(Result,PChar(S, T[k],L.D))
	end
  return Result
end

function IterTools.product(P::Array)
  T = ntuple(x->P[x], length(P))
  return IterTools.Product(T)
end
