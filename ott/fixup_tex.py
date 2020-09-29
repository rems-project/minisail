import tempfile, os, shutil,sys

start_syn=0

for filename in sys.argv[1:]:

    with tempfile.NamedTemporaryFile(delete=False) as temp_file:
        with open(filename) as infile:
            for line in infile:

                if line.startswith("\section{Type System}"):
                    line = "\ottmetavars\\\\[0pt]\n\ottgrammar\\\\[5.0mm]\n" + line + "\n"
                    start_syn = 0

                if start_syn == 1 and line.startswith("\section{Syntax}"):
                    start_syn = 2
                    
                if start_syn == 1:
                    continue
                
                if line.startswith("\\newcommand{\\ottall"):
                    line = "\\newcommand{\\ottall}{\n"
                    start_syn=1
                

                temp_file.write(line)

    shutil.move(temp_file.name, filename)

