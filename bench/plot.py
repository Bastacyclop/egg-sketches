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

plots = [
  ("guided-blocking", (4, 3)),
  ("guided-parallel", (6, 3)),
  ("unguided-blocking", (4, 3)),
  ("unguided-parallel", (4, 3)),
]

for (i, (name, figsize)) in enumerate(plots):
    data = pd.read_csv(name + '.csv', sep=' ')

    data['skit'] = list(zip(data.sketch, data.iteration))
    data['index'] = [i for (i, _) in enumerate(zip(data.sketch, data.iteration))]

    # insert NaNs at discontinuities
    discontinuities = list(set(data.sketch.values))
    # print(data)
    nans = pd.DataFrame({
        "sketch": [s for s in discontinuities],
        "iteration": [max(data[data["sketch"] == s].iteration.values) + 1 for s in discontinuities],
        "index": [max(data[data["sketch"] == s].index.values) for s in discontinuities],
        "nodes": [np.nan for s in discontinuities],
        "classes": [np.nan for s in discontinuities],
        "rules": [np.nan for s in discontinuities],
        })
    frame = pd.concat([data, nans]).sort_values(by=['index', 'iteration'])
    # print(frame)

    plt.rc('axes', prop_cycle=
           (cycler('color', ['#1E88E5', '#FFC107', '#004D40']) +
            cycler('linestyle', ['-']) *
            cycler('marker', ['.', '+', 'x'])))
    fig, ax = plt.subplots(figsize=figsize, tight_layout = {'pad': 0})

    frame.plot("index", ["nodes", "classes", "rules"], ax=ax)

    maxColor='grey'
    maxY = max([max(data.nodes.values), max(data.classes.values), max(data.rules.values)])
    maxYC = math.ceil(maxY / 1000) * 1000
    (unitPrefixS, unitPrefixN) = ('M', 1000000) if (maxY > 1000000) or (name ==
            "unguided-parallel") else ('K', 1000) 
    prefixValue = lambda v: str(int(v / unitPrefixN)) + unitPrefixS
    print("max Y: ", maxY, " ~ ", maxYC)
    # plot max size
    if name != "unguided-parallel":
        plt.axhline(y=maxYC, color=maxColor, linestyle='--')
    if name == "guided-blocking":
        trans = transforms.blended_transform_factory(
            ax.get_yticklabels()[0].get_transform(), ax.transData)
        ax.text(0, maxYC, prefixValue(maxYC), color=maxColor, transform=trans, ha='right', va='center')

    # curve fitting
    def curveFun(x, a, b, c):
        return a * np.exp(-b * x) + c
    def plotCurve(xs, ys):
        optimizedParameters, pcov = opt.curve_fit(curveFun, xs, ys, maxfev=50000)
        xsbis = np.append(xs, [max(xs) + 1])
        ax.plot(xsbis, curveFun(xsbis, *optimizedParameters), linestyle=':')
    if name == "unguided-parallel":
        plotCurve(data['iteration'].values, data['nodes'].values)
        plotCurve(data['iteration'].values, data['classes'].values)
        plotCurve(data['iteration'].values, data['rules'].values)

    # plot sketch guides
    guideColor='#5500d4ff'
    periods = data[data.sketch.diff() != 0].index.values
    plt.vlines(periods[1:], ymax=maxYC, ymin=0, color=guideColor, linestyle='--')
    for (i, item) in enumerate(periods[1:]):
        plt.text(y=0.90*maxYC, x=item+0.5, s='sketch', color=guideColor)
        plt.text(y=0.80*maxYC, x=item+0.5, s='guide', color=guideColor)
        plt.text(y=0.70*maxYC, x=item+0.5, s='n°'+str(i+1), color=guideColor)

    plt.xlabel("iterations")
    ax.yaxis.set_major_formatter(FuncFormatter(lambda n, _: prefixValue(n)))
    if name == "unguided-parallel":
        plt.ylim((0, 4000000))
        plt.xticks(np.arange(data.skit.size + 1), np.arange(data.skit.size + 1))
    else:
        plt.xticks(np.arange(data.skit.size), [i for (_, i) in data.skit.values])
    ax.get_legend().remove()
    plt.savefig(name + '.pgf')
    plt.savefig(name + '.png')

    if i == 0:
        figleg = plt.figure(tight_layout = {'pad': 0}, figsize=(2, 1.5))
        patches, _labels = ax.get_legend_handles_labels()
        patches.append(mpl.lines.Line2D([0], [0], color="black", linestyle=":"))
        figleg.legend(patches, ["e-nodes", "e-classes", "rules", "prediction"])
        figleg.savefig("legend.pgf")
        figleg.savefig("legend.png")
