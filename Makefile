.PHONY: out compile clean

compile: out
	ghc src/Plugin.hs -dynamic-too -outputdir out 
	ghc src/Main.hs -package random -isrc -odir out -o out/Main -fconstraint-solver-iterations=10

out:
	mkdir -p out

clean:
	rm -rf out