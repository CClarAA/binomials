#function to create commuting birth and death ideals and superflous respectively 
#test functions for calculations with binomial ideals

###################################################################################
#
#	Commuting Birth and Death ideals
#
###################################################################################

function commutingBirthDeath(m::Int64,n::Int64)
	f=open("commutingBirthDeathText.jl","w")
	#first write the polynomial ring
	write(f,"R,(")
	for i=0:(m-1)
		for j=0:n
			write(f,"R")
			write(f,"$i")
			write(f,"$j")
			write(f,",")
		end
	end
	
	for i=1:m
		for j=0:n
			write(f,"L")
			write(f,"$i")
			write(f,"$j")
			write(f,",")
		end
	end

	for i=0:m
		for j=0:(n-1)
			write(f,"U")
			write(f,"$i")
			write(f,"$j")
			write(f,",")
		end
	end

	for i=0:(m-1)
		for j=1:n
			write(f,"D")
			write(f,"$i")
			write(f,"$j")
			write(f,",")
		end
	end

	for j=1:(n-1)
			write(f,"D$m$j,")
	end

	write(f,"D$m$n")	
	write(f,")=Singular.PolynomialRing(QabField(),[")
	for i=0:(m-1)
		for j=0:n
			write(f,"\"R$i$j\",")
		end
	end
	
	for i=1:m
		for j=0:n
			write(f,"\"L$i$j\",")
		end
	end

	for i=0:m
		for j=0:(n-1)
			write(f,"\"U$i$j\",")
		end
	end

	for i=0:(m-1)
		for j=1:n
			write(f,"\"D$i$j\",")
		end
	end

	for j=1:(n-1)
			write(f,"\"D$m$j\",")
	end

	write(f,"\"D$m$n\"]) \n")
		
	#now write the ideal 
	write(f,"I=Ideal(R,")
	for i=0:(m-1)
		for j=0:(n-1)
			write(f,"U$i$j*R$i$(j+1) - R$i$j*U$(i+1)$j,")
			write(f,"D$i$(j+1)*R$i$j - R$i$(j+1)*D$(i+1)$(j+1),")
			write(f,"D$(i+1)$(j+1)*L$(i+1)$j - L$(i+1)$(j+1)*D$i$(j+1),")
			write(f,"U$(i+1)$j*L$(i+1)$(j+1)-L$(i+1)$j*U$i$j,")
		end
	end

	write(f,"R(0))")
	
	close(f)
	run(`cat commutingBirthDeathText.jl`)
	run(`rm commutingBirthDeathText.jl`)
	
end


###################################################################################
#
#	Zusatz-Funktionen 
#
###################################################################################


function intersectionArray(A::Array{Singular.sideal,1})
	#intersects all ideals in an array
	if size(A,1)==0
		error("array is empty")
	end

	result=Ideal(base_ring(A[1]),base_ring(A[1])(1))

	for i=1:size(A,1)
		if typeof(A[i])!=Singular.sideal{Singular.spoly{Singular.n_unknown{QabElem}}}
			error("there is an element in array which is not an ideal")
		end
		result=Singular.intersection(result,A[i])
	end
	
	return result
end

function intersectionArray(A::Array{Any,1})
	#noch test einbauen ob auch wirklich nur ideale im array
	if size(A,1)==0
		error("array is empty")
	end
	
	result=Ideal(base_ring(A[1]),base_ring(A[1])(1))

	for i=1:size(A,1)
		if typeof(A[i])!=Singular.sideal{Singular.spoly{Singular.n_unknown{QabElem}}}
			error("there is an element in array which is not an ideal")
		end
		result=Singular.intersection(result,A[i])
	end
	
	return result
end

function stdArray(A::Array{Any,1})
	for i=1:size(A,1)
		A[i]=std(A[i])
	end
	return A
end

function binomialPrimaryDecompositionWithBCD(I::Singular.sideal, bcd::Array{Singular.sideal,1})
	#input: binomial ideal (pure difference) and a cellular decomposition bcd of I 
	#output: binomial primary ideals which form a not necessarily 
	#minimal primary decomposition of I

	#first compute a cellular decomposition of I
	cellComps=bcd
	
	C=Array{Singular.sideal}[]	#this will hold the set of primary components
	
	#now compute a primary decomposition of each cellular component 
	for J in cellComps
		C=[C; cellularPrimaryDecomposition(J)]
	end
	
	#remove redundancies 
	C=removeSomeRedundancies(C)

	return C		
end

function make_compatible(f::Singular.spoly,R::Singular.PolyRing)
	#makes that all coefficients are represented as elements in the same cyclotomic extension
	l=length(f)
	n=nemo(coeff(f,0)).c
	for i=1:l-1
		n=lcm(nemo(coeff(f,i)).c,n)
	end
	println(n)
	fnew=R(0)	
	Variables=Singular.gens(R)
	a=root_of_unity(QabField(),n)	
	for i=1:l
		A=make_compatible(a,nemo(lead_coeff(f)))
		#compute lead monomial of f
		exp=lead_exponent(f)
		monom=R(1)
		for j=1:Singular.ngens(R)
			monom=monom*Variables[j]^exp[j]
		end
		fnew=fnew+A[2]*monom
		f=f-nemo(lead_coeff(f))*monom
	end
	return fnew
end

function make_compatible(J::Singular.sideal)
	#coerce up the generators of an ideal to the same cyclotomic field, perhaps this helps 
	#so that the ideal intersection works
	#assume: the generators of both ideals all are represented with the same root of unity
	I=J
	if iszero(I)==true
		return I
	end
	
	if Singular.ngens(I)==1
		I[1]=make_compatible(I[1],I.base_ring)
	end

	for i=1:(Singular.ngens(I)-1)
		I[i]=make_compatible(I[i],I.base_ring)
		I[i+1]=make_compatible(I[i+1],I.base_ring)
		A=make_compatible(nemo(lead_coeff(I[i])),nemo(lead_coeff(I[i+1])))
		I[i]=I[i]+A[1]
		I[i]=make_compatible(I[i],I.base_ring)-A[1]
		println(I[i])
		I[i+1]=I[i+1]+A[1]
		I[i+1]=make_compatible(I[i+1],I.base_ring)-A[1]
		println(I[i+1])
	end
	return(I)
end

function make_compatible(I1::Singular.sideal,I2::Singular.sideal)
	I=make_compatible(I1)
	J=make_compatible(I2)
	if iszero(I)==true || iszero(J)==true
		return [I;J]
	end
	a=nemo(lead_coeff(I[1]))
	b=nemo(lead_coeff(J[1]))
	A=make_compatible(a,b)
	Variables=Singular.gens(I.base_ring)
	I[1]=I[1]+A[1]*Variables[1]
	J[1]=J[1]+A[2]*Variables[1]
	I=make_compatible(I)
	J=make_compatible(J)
	I[1]=I[1]-A[1]*Variables[1]
	J[1]=J[1]-A[2]*Variables[1]
	return [I;J]
end

function cellularAssociatedPrimesSet(I::Singular.sideal)
	#verwendet set of ideals aber klappt im moment leider noch nicht 
	#input: cellular binomial ideal (pure difference)
	#output: the set of associated primes of I
	
	if isUnital(I)==false
		error("input ideal is not a pure difference binomial ideal")
	end

	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	if I.isGB==false
		I=std(I)
	end
	
	Ass=Set{Singular.sideal}([])	#this will hold the set of associated primes of I
	Variables=Singular.gens(I.base_ring)
	U=cellularStandardMonomials(I)	#set of standard monomials
	
	#construct the ideal (x_i \mid i \in \Delta^c)
	idealDeltaC=Ideal(R,R(0))
	for i=1:Singular.ngens(I.base_ring)
		if (i in cell[2])==false
			idealDeltaC=idealDeltaC + Ideal(I.base_ring,Variables[i])
		end
	end		
	
	for m in U
		Im=Singular.quotient(I,Ideal(I.base_ring,m))
		Pm=partialCharacterFromIdeal(Im,I.base_ring)
		
		#now compute all saturations of the partial character Pm
		PmSat=PCharSaturateAll(Pm)					

		for P in PmSat
			push!(Ass,(idealFromCharacter(P, I.base_ring)+idealDeltaC))
			#Ass=[Ass; (idealFromCharacter(P, I.base_ring)+idealDeltaC)]
		end
	end

	return collect(Ass)
end

