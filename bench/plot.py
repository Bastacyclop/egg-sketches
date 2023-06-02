import matplotlib as mpl
mpl.use('pgf')
mpl.rcParams.update({
    "pgf.texsystem": "pdflatex",
    'font.family': 'serif',
    'font.size': 16,
    'text.usetex': True,
    'pgf.rcfonts': False,
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

plots = [
  "tile_1d_s",
  "tile_1d_r",
  "tile_1d",
  "tile_2d_s",
  "tile_2d_r",
  "tile_2d",
  "tile_3d_s",
  "tile_3d_r",
  "tile_3d",
]

data = pd.read_csv('bench/results.csv', skipinitialspace=True)
# data = data.astype({'iteration_number':'int', 'physical_memory':'int', 'virtual_memory':'int', 'e-nodes':'int', 'e-classes':'int', 'applied_rules':'int', 'total_time':'float', 'hook_time':'float', 'search_time':'float', 'apply_time':'float', 'rebuild_time':'float'})
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
    # ax.set_title(plots[i][0].replace('-', ' '))

    
    #data['x'] = list(accumulate(zip(data.sketch, data.iteration),
    #    lambda acc, si: acc if si[1] == 0 else acc + 1,
    #    initial=0))[1:]
    # print(data)

    print(frame)
    frame.plot('iteration_number', ["virtual_memory"], ax=ax)
    # "physical_memory", "e-nodes", "e-classes", "applied_rules", "total_time"

    maxColor='red'
    maxY = 8e9
    print("max Y: ", maxY)
    # plot max size
    ax.axhline(y=maxY, color=maxColor, linestyle='--')
    prefixValue = lambda v: str(int(v / 1e9)) + "Gb"
    ax.text(1, 10e9, prefixValue(maxY), color=maxColor, ha='right', va='bottom')
    # transform=trans

    # curve fitting
    def curveFun(x, a, b, c):
        # return a * np.exp(-b * x) + c
        return np.float64(a * np.exp(np.float128(b * x)) + c)
    def plotCurve(xs, ys):
        optimizedParameters, pcov = opt.curve_fit(curveFun, xs, ys, maxfev=50000)
        xsbis = np.append(xs, [max(xs) + 1])
        ax.plot(xsbis, curveFun(xsbis, *optimizedParameters), linestyle=':')
    if name == "tile_3d":
        plotCurve(frame['iteration_number'].values, frame['virtual_memory'].values)

    #ax.set_xlim((0, 22))
    ax.set_xlabel("iterations")
    # ax.set_xlim(data["iteration_number"].min(), data["iteration_number"].max() + 1)
    ax.set_ylim(data["virtual_memory"].min(), maxY * 2.5)
    ax.set_yscale('log')
    # ax.yaxis.set_major_formatter(FuncFormatter(lambda n, _: prefixValue(n)))
    ax.xaxis.set_major_formatter(FuncFormatter(lambda n, _: str(int(n))))
    plt.xticks(frame["iteration_number"])
    
    if name != "tile_3d":
        ax.get_legend().remove()
    else:
        patches, _labels = ax.get_legend_handles_labels()
        patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
        ax.legend(patches, ["memory", "estimate"])

    plt.savefig('bench/' + name + '.pgf')
    plt.savefig('bench/' + name + '.png')
    print("----")

for i, name in enumerate(plots):
    plotOne(i, name)

# if i == 0:
#     figleg = plt.figure(tight_layout = {'pad': 0}, figsize=(2, 1.5))
#     patches, _labels = ax.get_legend_handles_labels()
#     patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
#     figleg.legend(patches, ["e-nodes", "e-classes", "rules", "prediction"])
#     figleg.savefig("legend.pgf")
#     figleg.savefig("legend.png")
