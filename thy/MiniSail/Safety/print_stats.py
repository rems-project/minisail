import subprocess,os
from ms_files import FILES


dirname = os.path.dirname(__file__)
fname = os.path.join(dirname,"..", "..", "..", "..", "research" , "thesis", "isa_thy_stats.tex")
print fname

with open(fname,"w" ) as outf:
    outf.write ("\\begin{tabular}{|l|r|r|}\n")
    outf.write ("\\hline\n")
    outf.write ("File Name & Line Count & Lemma Count\\\\ \n")
    outf.write ("\\hline\n")

    total_lines = 0
    total_lemmas = 0
    for f in FILES:
        print("file {}".format(f))
        p = subprocess.Popen('wc -l {}'.format(f), shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for line in p.stdout.readlines():
            line = line.split(' ')
            line_cnt = line[0]
            total_lines += int(line_cnt)


        p = subprocess.Popen('grep -c "^lemma.*" {}'.format(f), shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for line in p.stdout.readlines():
            lemma_cnt = line.strip()
            total_lemmas += int(lemma_cnt)


        outf.write ("{} & {} & {} \\\\\n".format(f,line_cnt,lemma_cnt))

        if f == "Operational.thy":
            outf.write("\hdashline\n")

    outf.write ("\\hline\n")
    outf.write ("Totals & {} & {} \\\\\n".format(total_lines, total_lemmas))
    outf.write ("\\hline\n")
    outf.write ("\end{tabular}\n")
