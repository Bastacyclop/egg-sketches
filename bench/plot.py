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
print(data)

plt.rc('axes', prop_cycle=
       (cycler('color', ['#1E88E5', '#FFC107', '#004D40']) +
        cycler('linestyle', ['-']) *
        cycler('marker', ['.', '+', 'x'])))

def plotOne(i, name):
    fig, ax = plt.subplots(figsize=(6, 3), tight_layout = {'pad': 0})
    # ax.set_title(plots[i][0].replace('-', ' '))

    
    #data['x'] = list(accumulate(zip(data.sketch, data.iteration),
    #    lambda acc, si: acc if si[1] == 0 else acc + 1,
    #    initial=0))[1:]
    # print(data)

    frame = data.query("search_name == @name")
    print(frame)
    print(frame.columns)
    frame.plot('iteration_number', ["physical_memory", "virtual_memory"], ax=ax)
    # "e_nodes", "e_classes", "applied_rules", "total_time"

    maxColor='grey'
    maxY = 8e9
    print("max Y: ", maxY)
    # plot max size
    ax.axhline(y=maxY, color=maxColor, linestyle='--')
    ax.text(0, maxY, str(maxY / 1e9) + "Gb", color=maxColor, ha='right', va='center')
    # transform=trans

    # curve fitting
    def curveFun(x, a, b, c):
        return a * np.exp(-b * x) + c
    def plotCurve(xs, ys):
        optimizedParameters, pcov = opt.curve_fit(curveFun, xs, ys, maxfev=50000)
        xsbis = np.append(xs, [max(xs) + 1])
        ax.plot(xsbis, curveFun(xsbis, *optimizedParameters), linestyle=':')
    if name == "tile_3d":
        plotCurve(data['iteration_number'].values, data['physical_memory'].values)
        plotCurve(data['iteration_number'].values, data['virtual_memory'].values)

    # ax.yaxis.set_major_formatter(FuncFormatter(lambda n, _: prefixValue(n)))

    #ax.set_xlim((0, 22))
    ax.set_xlabel("iterations")
    # plt.xticks(np.arange(data.skit.size), [i for (_, i) in data.skit.values])

    # if name != "tile_1d":
    #    ax.get_legend().remove()
    # else:
    patches, _labels = ax.get_legend_handles_labels()
    patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
    ax.legend(patches, ["pmem", "vmem", "estimate"])
    ax.set_yscale('log')
    ax.set_xlim(data["iteration_number"].min(), data["iteration_number"].max() + 1)
    ax.set_ylim(data["physical_memory"].min(), maxY * 1.5)

    plt.savefig('bench/' + name + '.pgf')
    plt.savefig('bench/' + name + '.png')

for i, name in enumerate(plots):
    plotOne(i, name)

# if i == 0:
#     figleg = plt.figure(tight_layout = {'pad': 0}, figsize=(2, 1.5))
#     patches, _labels = ax.get_legend_handles_labels()
#     patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
#     figleg.legend(patches, ["e-nodes", "e-classes", "rules", "prediction"])
#     figleg.savefig("legend.pgf")
#     figleg.savefig("legend.png")
