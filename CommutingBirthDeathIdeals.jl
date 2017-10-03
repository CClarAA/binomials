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
	
