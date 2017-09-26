#functions in this file:
#isCellular(I::Singular.sideal)
#saturate(I::Singular.sideal, J::Singular.sideal)
#cellularDecomp(I::Singular.sideal)
#isBinomial(f::Singular.spoly)
#isBinomialIdeal(I::Singular.sideal)
#lead_coeff(f::Singular.spoly)
#monomialFromVector(a::Array{Int64,1}, R::Singular.PolyRing)
#markov4ti2(L::fmpz_mat)
# "=="(I::Singular.sideal,J::Singular.sideal)
#isSubset(I::Singular.sideal,J::Singular.sideal)
#idealFromCharacter(P::PChar, R::Singular.PolyRing)
#partialCharacterFromIdeal(I::Singular.sideal, R::Singular.PolyRing)
#cellularStandardMonomials(I::Singular.sideal)
#witnessMonomials(I::Singular.sideal)
#cellularPrimaryDecomposition(I::Singular.sideal)
#cellularMinimalAssociatedPrimes(I::Singular.sideal)
#cellularAssociatedPrimes(I::Singular.sideal)
#cellularHull(I::Singular.sideal)


#neue Notationan eingearbeitet

###################################################################################
#
#	Hilfsfunktionen
#
###################################################################################

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

function isBinomial(f::Singular.spoly)
	if Singular.length(f)<=2
		return(true)
	else 
		return(false)
	end
end


function isBinomialIdeal(I::Singular.sideal)
	#compute reduced GB and check if all elements in the GB are binomials
	I=std(I,complete_reduction=true)

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
	nColMarkov=Int(helpArray[1,2])
	nRowMarkov=Int(helpArray[1,1])
	#println(nRowMarkov)
	
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

function monomialFromVector(a::Array{Int64,1}, R::Singular.PolyRing)
	#returns the monomial corresponding to an exponent vector
	Variables=Singular.gens(R)
	monom=R(1)
	for i=1:Singular.ngens(R)
		monom=monom*Variables[i]^a[i]
	end
	return monom
end

function lead_coeff(f::Singular.spoly)
	return(coeff(f,length(f)-1))
end

function matrixFromArray(A::Array{Int64,1})
	#returns a matrix over FlintZZ with the entries of A transposed
	Mat=zeros(Int64,size(A,1),1)
	MatFlint=matrix(FlintZZ,size(A,1),1,Mat)
	for i=1:size(A,1) 
		MatFlint[i,1]=A[i]
	end
	return(MatFlint)
end

function nemo(a::Singular.n_unknown{})
	#returns the nemo value of a Singular.n_unknown element
	return Singular.libSingular.julia(a.ptr)
end

import Base.==

function ==(I::Singular.sideal,J::Singular.sideal)
	if isSubset(I,J)==true && isSubset(J,I)==true
		return true
	else 
		return false
	end
end

function isSubset(I::Singular.sideal,J::Singular.sideal)
	#returns true if I is contained in J
	#else returns false
	if J.isGB==false
		J=std(J)
	end
	testIdeal=std(reduce(I,J))
	if Singular.ngens(testIdeal)==0 || testIdeal[1]==I.base_ring(0)
		return true
	end
	return false	
end

function removeSomeRedundancies(A::Array{Any,1})
	#input:Array of ideals
	#output:Array of ideals consisting of some ideals less which give the same interseciton as
	#all ideals before
	
	Result=A

	for i=size(A,1):-1:1
		k=i-1
		flag=true
		while flag==true && k>0
			if isSubset(Result[k],Result[i])==true
				flag=false	#we can remove the ideal Result[i]
			end
			k=k-1
		end	
		if flag==false
			deleteat!(Result,i)
		end
	end

	for i=size(Result,1):-1:1
		k=i-1
		flag=true
		while flag==true && k>0
			if isSubset(Result[i],Result[k])==true
				flag=false 	#we can remove the ideal Result[k]
			else
				k=k-1
			end
		end
		if flag == false
			deleteat!(Result,k)
		end
	end

	return Result
end

function extractInclusionMinimalIdeals(A::Array{Any,1})
	#returns all ideals of A which are minimal with respect to inclusion
	#todo: sanity check -> check if all elements in A are ideals!	
	
	n=size(A,1)
	#work with a copy of A
	Result=A
	
	while n>0
		helpIdeal=Result[1]
		#now delete ideal from Array
		deleteat!(Result,1)
		flag=true 	#if ideal helpIdeal is redundant the flag is false
		for k=1:size(Result,1)
			if isSubset(Result[k],helpIdeal)==true
				flag=false
			end
		end
		if flag==true
			Result=[Result;helpIdeal]
		end
		n=n-1			
	end		
	return Result
end 

###################################################################################
#
#	Cellular-zeug

#
###################################################################################

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
	#satu=Ideal(I.base_ring)
	helpideal=Ideal(I.base_ring)
	
	for i=1:Singular.ngens(I.base_ring)
		helpideal=Ideal(I.base_ring,Variables[i])
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
	
	prodRingVarIdeal=Ideal(I.base_ring,prodRingVar)
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
		J=quotient(I,Ideal(I.base_ring,Variables[i]))
		#J=saturate(I,Ideal(R,Variables[i]))
		#if Singular.ngens(std(reduce(J[1],I)))!=0
		if Singular.ngens(std(reduce(J,I)))!=0
			return (false,i)
		end
		end		

	end
end


function cellularDecomp(I::Singular.sideal) #with less redundancies
	#input: binomial ideal I
	#output: a cellular decomposition of I

	if (isBinomialIdeal(I)==false)
		error("Input ideal is not binomial")
	end

	A=isCellular(I)
	if A[1]==true
		return [std(I)]
	end
	
	#choose a variable which is a zero divisor but not nilptent modulo I -> A[2] (if not dummer fall)
	#determine the power s s.t. (I:x_i^s)==(I:x_i^infty)
	satu=saturate(I,Ideal(I.base_ring,Singular.gens(I.base_ring)[A[2]]))
	s=satu[2]
	#now compute the cellular decomposition of the binomial ideals (I:x_i^s) and I+(x_i^s)
	#by recursively calling the algorithm
	Decomp=Singular.sideal[]
	I1=satu[1]
	I2=I+Ideal(I.base_ring,(Singular.gens(I.base_ring)[A[2]])^s)
	if I==I1
		error("I1 is equal I")
	end
	if I==I2
		error("I2 is equal I")
	end
	if I1==Ideal(I.base_ring,I.base_ring(1))
		println(I)
		println((Singular.gens(I.base_ring)[A[2]])^s)
		error("unit ideal appears for I1")
	end
	if I2==Ideal(I.base_ring,I.base_ring(1))
		println(I)
		println((Singular.gens(I.base_ring)[A[2]])^s)
		error("unit ideal appears for I2")
	end
	
	DecompI1=cellularDecomp(I1)
	DecompI2=cellularDecomp(I2)
	
	#now check for redundancies
	redTest=Ideal(I.base_ring,one(I.base_ring))
	redTestIntersect=Ideal(I.base_ring,one(I.base_ring))
	
	for i=1:size(DecompI1,1)
		redTestIntersect=Singular.intersection(redTest,DecompI1[i])
		if Singular.ngens(std(reduce(redTest,std(redTestIntersect))))!=0
			#ideal not redundant
			Decomp=[Decomp;DecompI1[i]]
		end
		redTest=redTestIntersect
	end
	for i=1:size(DecompI2,1)
		redTestIntersect=Singular.intersection(redTest,DecompI2[i])
		if Singular.ngens(std(reduce(redTest,std(redTestIntersect))))!=0
			#ideal not redundant
			Decomp=[Decomp;DecompI2[i]]
		end
		redTest=redTestIntersect
	end
		
	return Decomp
end 


function cellularDecomp2(I::Singular.sideal) #with redundancies
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
	satu=saturate(I,Ideal(I.base_ring,Singular.gens(I.base_ring)[A[2]]))
	s=satu[2]

	#now compute the cellular decomposition of the binomial ideals (I:x_i^s) and I+(x_i^s)
	#by recursively calling the algorithm
	Decomp=Singular.sideal[]
	I1=satu[1]
	println(satu)
	println(A[2])
	I2=I+Ideal(I.base_ring,(Singular.gens(I.base_ring)[A[2]])^s)
	
	Decomp=[Decomp; cellularDecomp(I1)]
	Decomp=[Decomp; cellularDecomp(I2)]

	return Decomp
end 


###################################################################################
#
#	partial characters and ideals
#
###################################################################################


# mit #= beginnt multiline comment 
function idealFromCharacter(P::PChar, R::Singular.PolyRing)
	@assert cols(P.A)==Singular.ngens(R)

	#test if the domain of the partial character is the zero lattice
	Zero=matrix(FlintZZ,1,cols(P.A),zeros(Int64,1,cols(P.A)))
	if rows(P.A)==1 && LatticeEqual(P.A,Zero)==true
		return Ideal(R,zero(R))
	end
	

	#now case if P.A is the identity matrix 
	#then the ideal generated by the generators of P.A suffices and gives the whoe ideal I_+(P)
	#note that we can only compare the matrices if P.A is a square matrix
	if cols(P.A)==rows(P.A)
		id=convert(Array{Int64},eye(cols(P.A)))
		ID=matrix(FlintZZ,cols(P.A),cols(P.A),id)
		if P.A==ID
			return(makeBinomials(P,R))	
		end
	end


	#now check if the only values of P taken on the generators of the lattice is one
	#then we can use markov bases
	#simple test
	test=true
	i=1
	Variables=Singular.gens(R)
	I=Ideal(R,zero(R))

	while test==true && i<=size(P.b,1)
		if P.b[i]!=QabField()(1)
			#in this case there is a generator g for which P(g)!=1
			test=false
		end
		i=i+1
	end
	
	if test==true
		#then we can use markov bases to get the ideal
		A=markov4ti2(P.A)
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
			I=I+Ideal(R,monomial1-monomial2)
		end	
		return I
	end


	#now consider the last case where we have to saturate      
	I=makeBinomials(P,R)
	#now we have to saturate the ideal by the product of the ring variables
	varProduct=one(R)
	for i=1:Singular.ngens(R)
		varProduct=varProduct*Variables[i]
	end	

	return saturate(I,Ideal(R,varProduct))[1]

end 


function makeBinomials(P::PChar, R::Singular.PolyRing)
	#output: ideal generated by the binomials corresponding to the partial character P
	#This is not the ideal I_+(P)!!

	@assert cols(P.A)==Singular.ngens(R)
	nc=cols(P.A)	#number of columns
	nr=rows(P.A)	#number of rows
	Variables=Singular.gens(R)

	#-> we have nr binomial generators for the ideal

	I=Ideal(R,zero(R))

	for k=1:nr
			monomial1=one(R)
			monomial2=one(R)
			for s=1:nc
				if P.A[k,s]<0
					monomial2=monomial2*Variables[s]^(Int64(-P.A[k,s]))
				else 
					monomial1=monomial1*Variables[s]^(Int64(P.A[k,s])) 
				end
			end
			#the new generator for the ideal is monomial1-P.b[k]*monomial2

			I=I+Ideal(R,monomial1-P.b[k]*monomial2)
	end	
	

	return I
end

function partialCharacterFromIdeal(I::Singular.sideal, R::Singular.PolyRing)
	#input: cellular binomial ideal
	#output: the partial character corresponding to the ideal I \cap k[\mathbb{N}^\Delta]
	#neue Version bei der wir in den ersten zwei fällen das gleiche zurückgeben 
	
	#first test if the input ideal is really a cellular ideal
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")	
	end

	Delta=cell[2]	#cell variables
	if size(Delta,1)==0
		P=PChar(matrix(FlintZZ,1,Singular.ngens(R), zeros(Int64,1,Singular.ngens(R))), [QabField()(1)], Set{Int64}(Delta))
		return P	
	end	
	
	#now consider the case where Delta is not empty
	#fist compute the intersection I \cap k[\Delta]
	#for this use eliminate function from Singular. We first have to compute the product of all 
	#variables not in Delta
	
	prodDeltaC=R(1)
	Variables=Singular.gens(R)
	for i=1:Singular.ngens(R)
		if (i in Delta)==false
			prodDeltaC=prodDeltaC*Variables[i]
		end
	end
	J=Singular.eliminate(I, prodDeltaC)	
	if Singular.ngens(J)==0 || (Singular.ngens(J)==1 && J[1]== R(0))	
		#return another trivial character
		#lattice has only one generator, namely the zero vector
		P=PChar(matrix(FlintZZ,1,Singular.ngens(R), zeros(Int64,1,Singular.ngens(R))), [QabField()(1)], Set{Int64}(Delta))
		return P
	end
	#now case if J \neq 0
	#let ts be a list of minimal binomial generators for J
	I=std(I)
	ts=Array{Singular.spoly}[]
	for i=1:Singular.ngens(J)
		ts=[ts; J[i]]
	end	
	#vs=matrix(FlintZZ,1,Singular.ngens(R),zeros(Int64,1,Singular.ngens(R)))
	vs=zeros(Int64,Singular.ngens(R),1)
	images=QabElem[]
	for t in ts
		tCopy=t
		u=lead_exponent(t)
		m=monomialFromVector(u,R)
		tCopy=tCopy-m
		v=lead_exponent(tCopy)
		#now test if we need the vector uv
		uv=matrixFromArray(u-v)	#this is the vector of u-v
		vst=transpose(vs)
		vstMat=matrix(FlintZZ,size(vst,1), size(vst,2),vst)
		if(cansolve(transpose(vstMat),uv)[1]==false)	
			images=[images; nemo(-lead_coeff(tCopy))]
			#we have to save u-v as generator for the lattice
			#now concatenate the vector vs on on bottom of the matrix vs
			vs=[vs (u-v)]
		end
	end
	#now vs has a zero in the left column and we have to delete it
	#but first we have to transpose vs
	vs=transpose(vs)
	
	vs=vs[2:size(vs,1),1:size(vs,2)]	
	#now convert to matrix
	
	vsMat=matrix(FlintZZ,size(vs,1), size(vs,2),vs)
	#hier noch das ganze mit den erzeugern richtig machen
	#um zu testen ob ein vektor in einem gitter enthalten ist verwende
	#cansolve(B,testVector)[1]==false

	P=PChar(vsMat, images , Set{Int64}(Delta))
	return P
end 


function partialCharacterFromIdeal2(I::Singular.sideal, R::Singular.PolyRing)
	#input: cellular binomial ideal
	#output: the partial character corresponding to the ideal I \cap k[\mathbb{N}^\Delta]
	#das ist die alte version... evtl funktioniert die nicht so richtig aber ich bin mir 
	#nicht sicher ob die neue version richtig ist
	
	#first test if the input ideal is really a cellular ideal
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")	
	end
	
	Delta=cell[2]	#cell variables
	if size(Delta,1)==0
		#return trivial partial character
		P=PChar(matrix([fmpz(0)]),[QabField()(1)], Set{Int64}([]))
		return(P)	
	end	
	
	#now consider the case where Delta is not empty
	#fist compute the intersection I \cap k[\Delta]
	#for this use eliminate function from Singular. We first have to compute the product of all 
	#variables not in Delta
	
	prodDeltaC=R(1)
	Variables=Singular.gens(R)
	for i=1:Singular.ngens(R)
		if (i in Delta)==false
			prodDeltaC=prodDeltaC*Variables[i]
		end
	end

	println(prodDeltaC)
	J=Singular.eliminate(I, prodDeltaC)
	println(J)
	
	#test if J is the zero ideal, todo: noch genau überlegen wie das jetzt gelöst ist	
	if Singular.ngens(J)==0 || (Singular.ngens(J)==1 && J[1]== R(0))	
		#return another trivial character
		#lattice has only one generator, namely the zero vector
		P=PChar(matrix(FlintZZ,1,Singular.ngens(R), zeros(Int64,1,Singular.ngens(R))), [QabField()(1)], Set{Int64}(Delta))
		return P
	end
	
	#now case if J \neq 0
	#let ts be a list of minimal binomial generators for J
	I=std(I)
	ts=Array{Singular.spoly}[]
	for i=1:Singular.ngens(J)
		ts=[ts; J[i]]
	end	
	
	#vs=matrix(FlintZZ,1,Singular.ngens(R),zeros(Int64,1,Singular.ngens(R)))
	vs=zeros(Int64,Singular.ngens(R),1)
	images=QabElem[]
	for t in ts
		tCopy=t
		u=lead_exponent(t)
		m=monomialFromVector(u,R)
		tCopy=tCopy-m
		v=lead_exponent(tCopy)

		#now test if we need the vector uv
		uv=matrixFromArray(u-v)	#this is the vector of u-v
		vst=transpose(vs)
		vstMat=matrix(FlintZZ,size(vst,1), size(vst,2),vst)
		
		if(cansolve(transpose(vstMat),uv)[1]==false)	
			images=[images; nemo(-lead_coeff(tCopy))]
			#we have to save u-v as generator for the lattice
			#now concatenate the vector vs on on bottom of the matrix vs
			vs=[vs (u-v)]
		end
	end
	
	#now vs has a zero in the left column and we have to delete it
	#but first we have to transpose vs
	vs=transpose(vs)
	
	vs=vs[2:size(vs,1),1:size(vs,2)]	
	#now convert to matrix
	
	vsMat=matrix(FlintZZ,size(vs,1), size(vs,2),vs)
	#hier noch das ganze mit den erzeugern richtig machen
	#um zu testen ob ein vektor in einem gitter enthalten ist verwende
	#cansolve(B,testVector)[1]==false

	P=PChar(vsMat, images , Set{Int64}(Delta))
	return P
end 

###################################################################################
#
#	embedded associated lattice witnesses and hull
#
###################################################################################


function cellularStandardMonomials(I::Singular.sideal)
	#assume I is cellular
	#return the Standardmonomials of the ideal I \cap k[\mathbb{N}^\Delta], 
	#this are only finitely many!

	if I.isGB==false
		I=std(I)
	end
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	R=Singular.base_ring(I)

	#now we start computing the standardmonomials
	#first determine the set Delta^c of noncellular variables
	DeltaC=Array{Int64}[]
	for i=1: Singular.ngens(R)
		if (i in cell[2])==false
			DeltaC=[DeltaC;i]
		end
	end
	
	#eliminate the variables in Delta
	prodDelta=R(1)
	Variables=Singular.gens(R)
	for i in cell[2]
		prodDelta=prodDelta*Variables[i]
	end
	
	J=Singular.eliminate(I, prodDelta)

	leadIdeal=lead(J)
	leadIdeal=std(leadIdeal)
	mon=Array{Singular.spoly}[]	#this will hold set of standard monomials	
	
	for i in DeltaC
		flag=true
		d=1
		while flag ==true
			if reduce(Variables[i]^d,I) == 0
				flag=false
			else
				mon=[mon;Variables[i]^d]
				d=d+1
			end
		end
	end 

	#next step is not implemented effectively but it works (Verbessern irgendwann)
	moncopy=mon
	
	for i in subsets(mon)
		testmon=R(1)
		for l in i 
			testmon=testmon*l
		end
		
		if reduce(testmon,I) != 0 && (testmon in moncopy)==false && testmon != R(1)
			moncopy=[moncopy;testmon]
		end
	end

	#noch das monom 1 hinzufügen... evtl gibt das aber auch probleme?!?
	moncopy=[moncopy; R(1)]
					
	return moncopy
end


function witnessMonomials(I::Singular.sideal)
	#input: cellular binomial ideal
	#output M_{emb}(I) (not the ideal, but the generators of it in an array)
	#test if input ideal is cellular
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	R=Singular.base_ring(I)
	Delta=cell[2]
	
	#compute the pChar corresponding to I and the standard monomials of I \cap k[N^Delta]
	P=partialCharacterFromIdeal(I, R)
	M=cellularStandardMonomials(I)	#array of standard monomials, this is our to-do list
	Memb=Singular.spoly[]	#this will hold our set of witness monomials
	Iquotm=Ideal(R,R(0))
	Pquotm=partialCharacterFromIdeal(I, R)

	while size(M,1)!=0
		Iquotm=Singular.quotient(I,Ideal(R,M[1]))
		Pquotm=partialCharacterFromIdeal(Iquotm, R)
		if rank(Pquotm.A)>rank(P.A)
			Memb=[Memb;M[1]]
		end
		deleteat!(M,1)
	end	
	
	return(Memb)
end		

function cellularHull(I::Singular.sideal)
	#input: cellular binomial ideal 
	#ouput: hull(I), the intersection of all minimal primary components of I

	#by theorems we know that Hull(I)=M_emb(I)+I
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end
	
	#now construct the ideal M_emb with the abouve algorithm witnessMonomials
	Memb=Ideal(I.base_ring,R(0))	#this will hold the ideal M_emb(I)
	M=witnessMonomials(I)
	
	for m in M
		Memb=Memb + Ideal(R,m)
	end
	
	return (I+Memb)	
end



###################################################################################
#
#	associated primes
#
###################################################################################	

function cellularAssociatedPrimes(I::Singular.sideal)
	#input: cellular binomial ideal
	#output: the set of associated primes of I
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	if I.isGB==false
		I=std(I)
	end
	
	Ass=Array{Singular.sideal}[]	#this will hold the set of associated primes of I
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
		Pm=partialCharacterFromIdeal(Im,Im.base_ring)
		#now compute all saturations of the partial character Pm
		PmSat=PCharSaturateAll(Pm)					
		for P in PmSat
			Ass=[Ass; (idealFromCharacter(P, I.base_ring)+idealDeltaC)]
		end
	end

	#now check if there are superflous elements in Ass
	for i=size(Ass,1):-1:1
		j=i-1
		flag = false
		while (j>0 && flag==false)
			if Ass[j]==Ass[i]
			 	deleteat!(Ass,i)
			end
			j=j-1
		end
	end	
	
	return Ass
end


function cellularAssociatedPrimesSet(I::Singular.sideal)
	#verwendet set of ideals aber klappt im moment leider noch nicht 
	#input: cellular binomial ideal
	#output: the set of associated primes of I
	
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


function cellularMinimalAssociatedPrimes(I::Singular.sideal)
	#input: cellular binomial ideal
	#output: the set of minimal associated primes of I
	
	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	P=partialCharacterFromIdeal(I,I.base_ring)
	PSat=PCharSaturateAll(P)
	
	minAss=Array{Singular.sideal}[]	#this will hold the set of minimal associated primes
	
	#construct the ideal (x_i \mid i \in \Delta^c)
	Variables=Singular.gens(I.base_ring)
	idealDeltaC=Ideal(R,R(0))
	for i=1:Singular.ngens(I.base_ring)
		if (i in cell[2])==false
			idealDeltaC=idealDeltaC + Ideal(I.base_ring,Variables[i])
		end
	end	

	for Q in PSat
		minAss=[minAss; (idealFromCharacter(Q,I.base_ring)+idealDeltaC)]
	end
		
	return minAss
end

function binomialAssociatedPrimes(I::Singular.sideal)
	#input: binomial ideal
	#output: the associated primes, but only implemented effectively in the cellular case	
	#in the noncellular case compute a primary decomp and take radicals
	
	cell=isCellular(I)
	if cell[1]==true
		return cellularAssociatedPrimes(I)
	end
		
	#now consider the case when I is not cellular and compute a primary decomposition
	PD=binomialPrimaryDecomposition(I)
	
	#todo: take radicals and delete the superfluous elements from the array
		
	return 1
	
end


###################################################################################
#
#	primary decomposition
#
###################################################################################


function cellularPrimaryDecomposition(I::Singular.sideal)    #algorithm from macaulay2
	#input: cellular binomial ideal in k[x] where k algebraically closed of characterstic 0
	#output: binomial primary ideals which form a minimal primary decomposition of I

	cell=isCellular(I)
	if cell[1]==false
		error("input ideal is not cellular")
	end

	#compute associated primes
	Ass=cellularAssociatedPrimes(I)
	C=Singular.sideal[]	#this will hold the set of primary components
	
	#compute product of all non cellular variables and the product of all cell variables
	prodDeltaC=R(1)	
	prodDelta=R(1)
	Variables=Singular.gens(I.base_ring)
	for i=1:Singular.ngens(R)
		if (i in cell[2])==false
			prodDeltaC=prodDeltaC*Variables[i]
		else 
			prodDelta=prodDelta*Variables[i]
		end
	end
	
	for P in Ass
		helpIdeal=I+eliminate(P,prodDeltaC)
		#now saturate the ideal with respect to the cellular variables
		helpIdeal=saturate(helpIdeal,Ideal(I.base_ring,prodDelta))
		C=[C; cellularHull(helpIdeal[1])]
	end
	return C
end

function binomialPrimaryDecomposition(I::Singular.sideal)
	#input: binomial ideal 
	#output: binomial primary ideals which form a not necessarily 
	#minimal primary decomposition of I

	#first compute a cellular decomposition of I
	cellComps=cellularDecomp(I)
	
	C=Array{Singular.sideal}[]	#this will hold the set of primary components
	
	#now compute a primary decomposition of each cellular component 
	for J in cellComps
		C=[C; cellularPrimaryDecomposition(J)]
	end
	
	#remove redundancies 
	C=removeSomeRedundancies(C)

	return C		
end

