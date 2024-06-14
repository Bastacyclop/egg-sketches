import matplotlib as mpl
mpl.use('pgf')
mpl.rcParams.update({
    "pgf.texsystem": "pdflatex",
    'font.family': 'serif', # use serif/main font for text elements
    'font.size': 16,
    'text.usetex': True, # use inline math for ticks
    'pgf.rcfonts': False, # don't setup fonts from rc parameters
    "pgf.preamble": "\n".join([
        r"\usepackage{pifont}",
        #r"\usepackage{amssymb}",
        #r"\usepackage{marvosym}",
        r"\DeclareUnicodeCharacter{2714}{\ding{51}}",
        r"\DeclareUnicodeCharacter{2718}{\ding{55}}",
        #r"\DeclareUnicodeCharacter{2718}{\smallsetminus}",
        #r"\DeclareUnicodeCharacter{2718}{\Emailct}",
        #r"\DeclareUnicodeCharacter{2718}{\raisebox{\depth}{\scalebox{1}[-1]{\Lightning}}}",
        #ifysm/marvosym \Lightning
        #r"\setmainfont{DejaVu Serif}",  # serif font via preamble
    ])
})
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
import matplotlib.transforms as transforms
import numpy as np
import pandas as pd
import math
from cycler import cycler
import scipy.optimize as opt
from functools import reduce
from itertools import accumulate
import sys

# TODO: argument
workdir = sys.argv[1]
data = pd.read_csv(workdir + "/results.csv", skipinitialspace=True)
data = data.astype({'iteration_number':'int', 'physical_memory':'int', 'virtual_memory':'int', 'e-nodes':'int', 'e-classes':'int', 'applied_rules':'int', 'total_time':'float', 'hook_time':'float', 'search_time':'float', 'apply_time':'float', 'rebuild_time':'float', 'found':'bool'})
#print(data)

fig, ax = plt.subplots(tight_layout = {'pad': 0.3}, dpi=200)
fig.set_figwidth(6)
fig.set_figheight(2)

def datapoint(search, time_col):
    return data.query("search_name == @search")[time_col].sum()

time_cols = ['hook_time', 'search_time', 'apply_time', 'rebuild_time']
searches = data['search_name'].unique()
weight_counts = {
    time_col.split("_")[0] : np.array([ datapoint(search, time_col) for search in searches ])
    for time_col in time_cols
}
print(weight_counts)

width = 0.5
stacked = np.zeros(len(searches))
for time_col, weight_count in weight_counts.items():
    ax.barh(searches, weight_count, width, label=time_col, left=stacked)
    stacked += weight_count

ax.legend(loc="upper right")
ax.invert_yaxis()

plt.savefig(workdir + '/time.pgf')
plt.savefig(workdir + '/time.png')