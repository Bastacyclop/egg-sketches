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

workdir = sys.argv[1]
data = pd.read_csv(workdir + "/results.csv", skipinitialspace=True)
data = data.astype({'iteration_number':'int', 'physical_memory':'int', 'virtual_memory':'int', 'e-nodes':'int', 'e-classes':'int', 'applied_rules':'int', 'total_time':'float', 'hook_time':'float', 'search_time':'float', 'apply_time':'float', 'rebuild_time':'float', 'found':'bool'})
#print(data)

plt.rc('axes', prop_cycle=
       (cycler('color', ['#1E88E5']) + #, '#FFC107', '#004D40']) +
        cycler('linestyle', ['-']) *
        cycler('marker', ['.']))) #, '+', 'x'])))

def plotOne(i, name):
    print("-- processing '" + name + "' --")
    frame = data.query("search_name == @name")

    fig, ax = plt.subplots(tight_layout = {'pad': 0.3}, dpi=200)
    fig.set_figwidth(max(1 + (frame["iteration_number"].max() / 2), 2))
    fig.set_figheight(3)

    
    #data['x'] = list(accumulate(zip(data.sketch, data.iteration),
    #    lambda acc, si: acc if si[1] == 0 else acc + 1,
    #    initial=0))[1:]
    # print(data)

    print(frame)
    frame.plot('iteration_number', ["virtual_memory"], ax=ax)
    # "physical_memory", "e-nodes", "e-classes", "applied_rules", "total_time"
    found_in_frame = frame.loc[frame['found'] == True]
    #for _, found_row in found_in_frame.iterrows():
    #    ax.text(found_row['iteration_number'], found_row['virtual_memory'], "✔", color="green", ha='right', va='bottom')
    
    # transform=trans

    # curve fitting
    def curveFun(x, a, b, c):
        # return a * np.exp(-b * x) + c
        return np.float64(a * np.exp(np.float128(b * x)) + c)
    def curveFunInverse(y, a, b, c):
        return np.log((y - c) / a) / b
    def plotCurve(xs, ys):
        optimizedParameters, pcov = opt.curve_fit(curveFun, xs, ys, maxfev=50000)
        # ax.text(curveFunInverse(8e9, *optimizedParameters), 8e9, "✘", color="black", ha='center', va='top')
        xsbis = np.array([max(xs), max(xs) + 1]) # np.append(xs, )
        ax.plot(xsbis, curveFun(xsbis, *optimizedParameters), linestyle=':')

    not_found = found_in_frame.shape[0] == 0
    it_symbol = "✔"
    last_iteration = frame['iteration_number'].max()
    if not_found:
        plotCurve(frame['iteration_number'].values, frame['virtual_memory'].values)
        it_symbol = "✘"
        last_iteration += 1

    # plot max size
    maxColor='red'
    maxY = 8e9
    print("max Y: ", maxY)
    ax.axhline(y=maxY, color=maxColor, linestyle='--')
    prefixValue = lambda v: str(int(v / 1e9)) + "Gb"
    ax.text(1, 10e9, prefixValue(maxY), color=maxColor, ha='left', va='bottom')

    #ax.set_xlim((0, 22))
    ax.set_xlabel("iterations")
    # ax.set_xlim(data["iteration_number"].min(), data["iteration_number"].max() + 1)
    ax.set_ylim(data["virtual_memory"].min(), maxY * 2.5)
    ax.set_yscale('log')
    # ax.yaxis.set_major_formatter(FuncFormatter(lambda n, _: prefixValue(n)))

    def xformat(n, _):
        if n == last_iteration:
            return it_symbol
        else:
            return str(int(n))
    ax.xaxis.set_major_formatter(FuncFormatter(xformat))
    plt.xticks(range(1, last_iteration + 1))
    if not_found:
        plt.gca().get_xticklabels()[-1].set_color('red')
    else:
        plt.gca().get_xticklabels()[-1].set_color('green')
    
    if name != "tile_3d":
        ax.get_legend().remove()
    else:
        patches, _labels = ax.get_legend_handles_labels()
        patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
        ax.legend(patches, ["memory", "estimate"])

    plt.savefig(workdir + '/' + name + '.pgf')
    plt.savefig(workdir + '/' + name + '.png')
    print("----")

for i, name in enumerate(data['search_name'].unique()):
    plotOne(i, name)

# if i == 0:
#     figleg = plt.figure(tight_layout = {'pad': 0}, figsize=(2, 1.5))
#     patches, _labels = ax.get_legend_handles_labels()
#     patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
#     figleg.legend(patches, ["e-nodes", "e-classes", "rules", "prediction"])
#     figleg.savefig("legend.pgf")
#     figleg.savefig("legend.png")
