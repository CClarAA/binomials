#functions in this file:
#isCellular(I::Singular.sideal)
#saturate(I::Singular.sideal, J::Singular.sideal)
#cellularDecomp(I::Singular.sideal)
#isBinomial(f::Singular.spoly)
#isBinomialIdeal(I::Singular.sideal)
#markov4ti2(L::fmpz_mat)
#idealFromCharacter(P::PChar, R::Singular.SingularPolyRing)

function isCellular(I::Singular.sideal)
	#output: the decision true/false whether I is cellular or not, I binomial ideal 
	#if it is cellular, return true, cellular variables
	if I.isGB==false	
		I=std(I)
	end
	
	if (isBinomialIdeal(I)==false)
		error("Input ideal is not binomial")
	end

	if Singular.ngens(I)==0
		#trivial case, I=0?! uninteressant -> doof
		return(false,-1)
	end

	if I[1]==1
		return(false,-1)
	end
	
	DeltaC=Int64[]
	Delta=Int64[]
	Variables=Singular.gens(I.base_ring)
	#satu=SingularIdeal(I.base_ring)
	helpideal=SingularIdeal(I.base_ring)
	
#	for i=1:Singular.ngens(I.base_ring)
#		helpideal=SingularIdeal(I.base_ring,Variables[i])
#		satu=saturate(I,helpideal)
#		if (std(satu[1])[1])==1
#			#println("j")
#			push!(DeltaC,i)
#		end
#	end
	
	for i=1:Singular.ngens(I.base_ring)
		helpideal=SingularIdeal(I.base_ring,Variables[i])
		satu=saturate(I,helpideal)
		if (std(satu[1])[1])!=1
			push!(Delta,i)
		end
	end
	
	#compute product of ring variables in Delta
	prodRingVar=one(I.base_ring)
	for k in Delta
		prodRingVar=prodRingVar*Variables[k]
	end
	
	prodRingVarIdeal=SingularIdeal(I.base_ring,prodRingVar)
	J=saturate(I,prodRingVarIdeal)
	#println(J)
	#println(Singular.ngens(std(reduce(J[1],I))))
	if Singular.ngens(std(reduce(J[1],I)))==0
		#then I==J[1]
		#in this case I is cellular with respect to Delta
		return(true,Delta)
	elseif (std(reduce(J[1],I))[1])==0 
		#then I==J[1]
		#in this case I is cellular with respect to Delta
		return(true,Delta)
	else
		for i in Delta
		J=quotient(I,SingularIdeal(I.base_ring,Variables[i]))
		#J=saturate(I,SingularIdeal(R,Variables[i]))
		#if Singular.ngens(std(reduce(J[1],I)))!=0
		if Singular.ngens(std(reduce(J,I)))!=0
			return (false,i)
		end
		end		

	end
end


function saturate(I::Singular.sideal, J::Singular.sideal)
	flag=true
	if I.base_ring!=J.base_ring
		return("Error: I and J not defined over the same ring")
	end
 	If=I
	k=0
	Iff=I
	while flag
		Iff=quotient(If,J)
		if Iff[1]==1 
			return([Iff,k+1])
		end
		if Singular.ngens(std(reduce(Iff,std(If))))==0
			return([Iff,k])
		end
		if std(reduce(Iff,std(If)))[1]==0
			return([Iff,k])
		end
		If=Iff
		k=k+1
	end	
end


function cellularDecomp(I::Singular.sideal)
	#input: binomial ideal I
	#output: a cellular decomposition of I

	if (isBinomialIdeal(I)==false)
		error("Input ideal is not binomial")
	end

	A=isCellular(I)
	if A[1]==true
		return [I]
	end
	
	#choose a variable which is a zero divisor but not nilptent modulo I -> A[2] (if not dummer fall)
	#determine the power s s.t. (I:x_i^s)==(I:x_i^infty)
	satu=saturate(I,SingularIdeal(I.base_ring,Singular.gens(I.base_ring)[A[2]]))
	s=satu[2]

	#now compute the cellular decomposition of the binomial ideals (I:x_i^s) and I+(x_i^s)
	#by recursively calling the algorithm
	Decomp=Singular.sideal[]
	I1=satu[1]
	println(satu)
	println(A[2])
	I2=I+SingularIdeal(I.base_ring,(Singular.gens(I.base_ring)[A[2]])^s)
	
	Decomp=[Decomp; cellularDecomp(I1)]
	Decomp=[Decomp; cellularDecomp(I2)]

	return Decomp
end 


function isBinomial(f::Singular.spoly)
	if Singular.length(f)<=2
		return(true)
	else 
		return(false)
	end
end


function isBinomialIdeal(I::Singular.sideal)
	if I.isGB==false	
		I=std(I)
	end

	for i=1:Singular.ngens(I)
		if isBinomial(I[i])==false
			return(false)
		end
	end
	return(true)
end 


function markov4ti2(L::fmpz_mat)
	#sanity checks noch einbauen!!
	nc=cols(L)
	nr=rows(L)
	#have to prepare an input file for 4ti2
	#create the file julia4ti2.lat
	#f=open("julia4ti2.mat","r")
	f=open("julia4ti2.lat","w")
	write(f,"$nr ")
	write(f,"$nc \n")

	for i=1:nr
		for j=1:nc
			write(f,"$(L[i,j]) ")
		end
		write(f,"\n")
	end		
	close(f)
	
	#now we have the file julia4ti2.lat in the current working directory
	#can run 4ti2 with this input file to get a markov basis
	run(`/usr/bin/markov julia4ti2`)
	#this creates the file julia4ti2.mar with the markov basis
	
	#numbers = readdlm("julia4ti2.mat")
	
	#now we have to get the matrix from julia4ti2.mat in julia
	#this is an array of thype Any
	#helpArray=readdlm("julia4ti2.mar",Int64)
	helpArray=readdlm("julia4ti2.mar")
	sizeHelpArray=size(helpArray)
	
	#the size of the markov basis matrix is
	nColMarkov=helpArray[1,2]
	nRowMarkov=helpArray[1,1]
	println(nRowMarkov)
	
	#now we have convert the lower part of the array helpArray into an Array of type Int64
	helpArrayInt=Array(Int64,nRowMarkov,nColMarkov)
	
	for i=2:(nRowMarkov+1)
		for j=1:nColMarkov
		helpArrayInt[i-1,j]=helpArray[i,j]
		end
	end
	
	#remove constructed files 
	run(`rm julia4ti2.lat`)
	run(`rm julia4ti2.mar`)	
	
	#now we have to convert this integer array into a FlintZZ matrix
	#braucht man das wirklich oder unnötig?? evtl Int64 besser...
	#Markov=Matrix(FlintZZ,nRowMarkov,nColMarkov,helpArrayInt)
	return helpArrayInt
end

# mit #= beginnt multiline comment 
#= function idealFromCharacter(P::PChar, R::Singular.SingularPolyRing)
	@assert cols(P.A)==Singular.ngens(R)

	#test if the domain of the partial character is the zero lattice
	Zero=Matrix(FlintZZ,1,cols(P.A),zeros(Int64,1,cols(P.A)))
	if rows(P.A)==1 && LatticeEqual(P.A,Zero)==true
		return SingularIdeal(R,zero(R))
	end
	
	#now check if the only values of P taken on the generators of the lattice is one
	
	#so geht das leider nicht	
	#valueSet=Set{QabElem}(P.b)
	#println(valueSet)
	#note that valueSet can't be empty
	#oneSet=Set{QabElem}()
	#push!(oneSet,Qab(1))
	#if pop!(valueSet)==Qab(1) && isempty(valueSet)==true
		#in this case we can use markov bases to get the result
		#return 5
	#end
	
	#now case if P.A is the identity matrix 
	ident=convert(Array{Int64},eyes(cols(P.A)))
	if P.A==identity

	#simple test
	test=true
	i=1
	Variables=Singular.gens(R)
	I=SingularIdeal(R,zero(R))

	while test==true && i<=size(P.b,1)
		if P.b[i]!=Qab(1)
			#in this case there is a generator g for which P(g)!=1
			test=false
		end
		i=i+1
	end
	
	if test==true
		#then we can use markov bases to get the ideal
		A=markov4ti2(P.A')
		#now get the ideal corresponding to the computed markov basis
		nr=size(A,1)	#number of rows
		nc=size(A,2)	#number of columns
		#-> we have nr generators for the ideal
		#for each row vector compute the corresponding binomial
		for k=1:nr
			monomial1=one(R)
			monomial2=one(R)
			for s=1:nc
				if A[k,s]<0
					monomial2=monomial2*Variables[s]^(-A[k,s])
				else 
					monomial1=monomial1*Variables[s]^(A[k,s]) 
				end
			end
			#the new generator for theideal is monomial1-minomial2
			I=I+SingularIdeal(R,monomial1-monomial2)
		end	
		return I
	end
	#now consider the last case where we have to saturate      
		
	return 1

end =#
