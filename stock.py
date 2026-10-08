"""
Chess PGN Analyzer — Stockfish GUI
Python 3.10+

Features:
- Paste/open PGN
- Load a game and browse it on the board WITHOUT running the engine
- Full-game Stockfish analysis (depth or time based), cancellable mid-run
- MultiPV
- CPL and approximate accuracy
- Move classification (with color-coded result rows)
- Critical positions and principal variations
- Evaluation graph (always in White's POV, with colored fill)
- Interactive board with last-move highlight, correct piece contrast,
  best-move arrow overlay, board flip and an evaluation bar
- Keyboard navigation (Left/Right/Home/End)
- Persisted Stockfish settings between sessions
- Export analysis to HTML/CSV

Install:
    pip install python-chess matplotlib pillow

Then install Stockfish separately and point the GUI to stockfish.exe.

Piece artwork: the board renders solid, minimalist pieces from the classic
"Cburnett" set (CC BY-SA 3.0, Colin M. L. Burnett), embedded as base64 PNGs
below (rendered once from the SVGs bundled with python-chess). If Pillow
isn't installed, the app falls back to text glyphs automatically.
"""

import base64
import csv
import io
import json
import math
import os
import statistics
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

import chess
import chess.pgn
import chess.engine

from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

try:
    from PIL import Image, ImageTk
    PIECE_IMAGES_AVAILABLE = True
except ImportError:
    PIECE_IMAGES_AVAILABLE = False


# ----------------------------
# Constants
# ----------------------------

MATE_SCORE = 100000

CLASS_COLORS = {
    "Excelente": "#d9f2d9",
    "Bom": "#eaffea",
    "Imprecisão": "#fff5b3",
    "Erro": "#ffe0b3",
    "Blunder": "#ffcccc",
}

PIECE_SYMBOLS = {
    (chess.PAWN, chess.WHITE): "♙", (chess.PAWN, chess.BLACK): "♟",
    (chess.KNIGHT, chess.WHITE): "♘", (chess.KNIGHT, chess.BLACK): "♞",
    (chess.BISHOP, chess.WHITE): "♗", (chess.BISHOP, chess.BLACK): "♝",
    (chess.ROOK, chess.WHITE): "♖", (chess.ROOK, chess.BLACK): "♜",
    (chess.QUEEN, chess.WHITE): "♕", (chess.QUEEN, chess.BLACK): "♛",
    (chess.KING, chess.WHITE): "♔", (chess.KING, chess.BLACK): "♚",
}

PIECE_KEY = {
    (chess.PAWN, chess.WHITE): "P", (chess.PAWN, chess.BLACK): "p",
    (chess.KNIGHT, chess.WHITE): "N", (chess.KNIGHT, chess.BLACK): "n",
    (chess.BISHOP, chess.WHITE): "B", (chess.BISHOP, chess.BLACK): "b",
    (chess.ROOK, chess.WHITE): "R", (chess.ROOK, chess.BLACK): "r",
    (chess.QUEEN, chess.WHITE): "Q", (chess.QUEEN, chess.BLACK): "q",
    (chess.KING, chess.WHITE): "K", (chess.KING, chess.BLACK): "k",
}

# Cburnett piece set (CC BY-SA 3.0, Colin M. L. Burnett), rendered once at
# build time from the SVGs bundled with python-chess (chess.svg.piece) and
# embedded here as base64 PNGs so the app ships as a single file with no
# extra runtime dependency beyond Pillow.
PIECE_PNG_B64 = {
    "P": (
        "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAAAABmJLR0QA/wD/AP+gvaeTAAAVGUlEQVR4nO3de3AVVZ4H8O+9yb25"
        "CeQJSJ6EIYhAEhGUndmSyMvXVhElsiTC7JYKK7phxGFqXXRnBV81IjW41OgibKEuD3HLHWvHcWSr3FVApVBcWIkB0QGBm3cIjySC"
        "EpKc/aNBZ6Ppc/qSPt23+/up6r/yE3+3+/x+93T37dMAERERERERERERERERERERERERERERERERERERERERERERERERERERERER"
        "EREREREREREREREREREREREREREREREREREREREREREREREREREREREREREREREREVE8G3xxI58KOJ0A2S4C4M8BTAVQDGAMgBEA"
        "MvrEnQYQBfAFgAMAdgL4EMA32jIlogGRBGAOgN8BOAdAxLidA/AfACou/ptE5GIZAH4JoBWxF31/WyuAfwCQru3TEJGSRAC/AHAG"
        "A1/4fbfTAB68+P8kIoddC2A/7C/8vtsnACZp+HxE1I9FMC7S6S7+S9s3MGYDRKRRIoB/hXOF33d7ETwlINIiGcDv4XzR993egHHL"
        "keIIfwcQXxIBvA7gtpj+48RETJgwAWPGjEFBQQFSU1MBAJ2dnairq8Pnn3+OmpoadHd3x5rfGzBuP/bE+g8QUf9egsVv5kgkIubN"
        "myfefPNN0dnZKWQ6OjrEG2+8Ie68804RiURimQn8i7a9QeQj1bBQiMnJyWLZsmWipaVFWvT9aW5uFg899FAsjWCRxv1C5HkTYeFq"
        "/0033SSOHDkSc+H3dfjwYTFz5kwrDeAcgKs17h8iz0oAsA8KhRcMBsVTTz0lenp6Bqz4L+np6RGPP/64CAQCqk1gD4Cg1j1F5EEP"
        "QKHgQqGQ2LJly4AXfl+bN28WoVBItQn8reZ9ReQpqQBOQuGbX0fxX7Jp0ybVmcAJAIM07zMiz3gICt+0TzzxhLbiv2T58uWqs4Bf"
        "aN5nRJ6QCKARkgKbMWOGLef8Mt3d3WLq1KkqDaAe/JUgkWWzICmupKQkcejQIe3Ff8kXX3whkpKSVJrArdr3HlGc+zdICmvp0qWO"
        "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"
        "gg=="
    ),
    "N": (
        "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"
    ),
    "B": (
        "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"
        "XxseMyENgFnNRgUiMUvP1UycOJGamhruu+8+SkpKKCkp4f7776empiZqejOa3NeGx0zIcGCzGowKHD161I56hER+fj4rVkRvBu3a"
        "2lozxaKjRXaYXAGY04jBc4ADBw7YVBVhYl9fQK4ATJEGwBwfcMhfAYMkFSKEampqjIoctKMeA4E0AObt9ffL/fv309LSYlddBq3T"
        "p0+bud36xI66DATSAJhX7e+XPp/PMN2WCN57772HUsqo2E476jIQSANg3hajAu+8844d9RjU1q1bZ6bY1nDXY6CQWVTMiwfO4KeP"
        "eXZ2NnV1dXg80gs1HC5evEhOTg7NzX6f77UCmUCPPbWKbnIFYF4nBjnnGxsb2bBhg03VGXzWrl1rFPwAFUjwmyYNgDVvGRV44YUX"
        "7KjHoPTrX//aTLG3w12PgURuAawZDtTjZ6SZ2+3m008/lRRhIfbJJ58wceJEoweAF9FzN0ZHv+wIIFcA1pwC3vVXwOfz8cwzz9hU"
        "ncHjmWeeMfP0/20k+EWY3YbBxBRut1vt3LnT4Sk0Bo4tW7Yol8tlZkKQb9p+NohBx4PuFej3ZCwvL1c9PT1Ox07U6+7uVpMmTTIT"
        "/PuQW1rL5H2VdQo9LuBb/grV19eTkJDAV77yFXtqNUA9/fTTvPbaa2aKLgMM+wgLEQpDgKMYfCvFxsaqDz/80Okv0ahVUVGhPB6P"
        "mW//z5CRrcJm8zAxffbw4cPVkSNHnI6lqLN//36VmZlpdpry220+9kLgAt7HxAk6duxYVV9f73RMRY3a2lo1atQos8G/3t7DLsTn"
        "rgM6MHGiFhYWqkOHDjkdWxFv//79VoL/AjIPoHDYUsydrCorK0tVVFQ4HWMRa926dSojI8Ns8CvgPluPtBBX4UJ3QDF10no8HvX4"
        "44+rzs5Op+MtYrS3t6tHHnlEud1uK8G/xs6DLIQ/XmA/5k9eVVxcrP785z87HXuOe/PNN1VhYaGVwFfAHmT2XxFhCtG5Ay2dzDNn"
        "zlSvv/666u7udjoWbdPd3a1Wr16tysvLrQa+Ak4AkT97SZSQnlOhNRGoRI9HtyQrK4vy8nLKysooKSmJiim6rPD5fOzbt48dO3aw"
        "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"
    ),
    "R": (
        "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"
    ),
    "Q": (
        "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"
        "YII="
    ),
    "K": (
        "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"
        "UaB34nhk2QAAAABJRU5ErkJggg=="
    ),
    "p": (
        "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAAAABmJLR0QA/wD/AP+gvaeTAAALOklEQVR4nO3dW4xdVR3H8e90pral"
        "pVSuhWIFiqAUqNwEEwkoPGgCiWAEI94wioIQ0Pji9cUYE+MlIQQjCcYYDS8mIsGQoES5GBEVJUK8oBAKBSnQFqhtoZfxYbWp7XSY"
        "c+bstf9r7/X9JP83g7+z5vz/XXufc9YGSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIkSZIk"
        "SZIkSZIkSZIkSZIkSZIkSZKkLlu0s1SpsegAym4+8HbgHGAlcBywHFiy1/9uPbAa+CfwCHA3cD+wpbWkkhoxD3gfcCuwCZicZW0C"
        "fgZctPO/KalgS4AvAWuZfdNPV2uBLwIHtPZqJA1kAvgcsIHmG3/vWg9cu/P/U1Kw04CHyN/4e9dfgFNbeH2SpnEF6SZd282/q7aQ"
        "dgOSWjQB/JC4xt+7bsZLAqkVC4DbiG/6vevnpI8cJWUyQWq06Gafrm4FxrO9eqlyPyC+yWeqm7K9eqliVxHf3IPWFZnWQKrSKcTe"
        "7R+2NgEnZ1kJqTLjwIPEN/Ww9QAwJ8N6SFW5hvhmnm1dmWE9pGrsD7xAfCPPtp4DFja+KmqMW7SyfRo4MDrECA4GPhUdQuqiCeBp"
        "4v8VH7Wewm8JFssdQLneDRweHaIBy4Dzo0No3xwA5fpQdIAGfSQ6gPbNI8HKNAGsI90E7IMNpPsB26ODaE/uAMp0Bv1pfkgnFXl2"
        "QIEcAGU6OzpABudEB9BUDoAyrYwOkMEJ0QE0lQOgTMdFB8jg+OgAmsoBUKbl0QEyeGN0AE3lAChTn24A7tLH19R5fgxYnjFgG/0b"
        "zjtIH29ORgfRbn17k/WFg1mtcACUZxLYHB0ig12PKFNBHABlWh8dIIN10QE0lQOgTKujA2TwRHQATeUAKNM/ogNk8Gh0AE3lACjT"
        "vdEBMrgnOoDUFSuIP8ij6TqqyQWS+u4J4pu2qerjPY1e8BKgXHdFB2jQL6MDSF1zFvH/cjdVZza8NlIVHiC+eUetPzW+KmqMlwBl"
        "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"
        "SY34Hy8N/xzMJ+7gAAAAAElFTkSuQmCC"
    ),
    "n": (
        "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"
    ),
    "b": (
        "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAAAABmJLR0QA/wD/AP+gvaeTAAASHklEQVR4nO3de3BWdX7H8XcuSBIN"
        "CREFQUAFQVAiIF63S72MtYqdtis4lfGy20Vpp+N2dXZtpTvtX51eaO3FGd06ZabOtrOtl1pr19p13V2sC4oZ1q7GO0s0RlwQiNwN"
        "SU7/+CYaQpLnnDznnO85z/m8Zr5DlAf4Puc83+9zLr/z+4GIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiI"
        "iIiIiIiIiIiIiIiIiMSgyjsBSc084FeBS4CFwHSgCfsM7AU+BF4HXgSeAd7xSVNE4lIH3A5sBYKI0QasASamnrWIlKUKuAXoJHrh"
        "D4/3gdXppi8i43Uq8DTlF/7weAqYkuL7EJGIzieeb/3R4j1gUWrvRkRCuwDYQ3LFPxi7gaUpvScRCWEu8DHJF/9g7ATOSuWdiciY"
        "6oFXSa/4B+MV7C6DiDi6j/SLfzD+IoX3JyKjOA/oxa8B9ADnJP4uRWREj+FX/IPxr4m/SxE5zhn4fvsPRi8wK9m3Kkmp9k5Axu1W"
        "oMY7CSyHm72TECma8YzvTyq2JPxeRWSIZqAP/8IfehowKdF3LInQKUA+LSZb+64GaPVOQqLL0odIwsviKLw53glIdGoA+ZTFp/JO"
        "8U5AolMDyKcTvBMYgYYF55AaQD71eCcwgiPeCUh0agD59LF3AiPY5Z2ARKcGkE8/905gBNu8ExApCo0DkFjoCCCfuoH/805iiK3A"
        "Pu8kJDo1gPx60juBIf7DOwGRojmTbJwG6GlAESeP498ANB+AiJNF+M8ItCDxdykio/ob/BqA5gQUcaZZgUUK7mzSXxdAT/+JZMhF"
        "2DLfSRf/HmBZSu9JRCJYDHxIcsX/AZr4o6JkYVJJicd84JvAJSQ3wKseaADasSMBEXE2F/hn0r0deBT4J2wwkog4mAZ8G7sXn/Yd"
        "gMH4FLgfzQYkkpp6YB328I1X4Q+PT4B7gIkJvm+Rwvt1YDv+BT9avAOsSOzdixTULOA/8S/wsPEEcHoiW0KkQKqBO4H9+Bd11NgH"
        "/C5QFftWESmAOcDz+BdyufEcMDvmbSNS0X6bfH7rjxafALfEuoVEKlAT8F38Czap+A7QGNvWEqkgrdhVdO8iTTreABbGtM1EKsJN"
        "wEH8izOt2A+sjGXLieRYFfCnQD/+RZl29AN/gu4SSEHVAY/gX4je8S9oBKEUTDOVcYsvrngOLSwiBTEVm07Lu+iyFm1kc9lzkdhM"
        "B97Ev9iyGq9iDVKk4kwH3sK/yLIe7cCp49zGIpk0BftgexdXXuIVYPK4trRIxjQCW/AvqrzFT7Dpx0RyqxZ4Bv9iyms8ieatlBz7"
        "B/yLKO/xd5G3ukgG3Il/8VRKrIm47UVcfRHfyTpDRUNDQ9DQ0OCeR4g4gi18IpJ5pwBd+BfNqHHllVcGL730UtDX1xf09fUFL774"
        "YnDFFVe451UiOtCdAcm4KuB7+BfLqHH99dcHvb29wXC9vb3Bdddd555fiXg8+i4RSc/v4V8ko0ZNTU3w/vvvH1f8gzo6OoLq6mr3"
        "PEvEV8exX0QSdzYZf6Z/8eLFoxb/oNbWVvc8S8Qn2CzJEoOk1pArmirgITI+cGXKlNLP2oR5jbNJ2IpIEgM1gHjcAlzunUQpVVWl"
        "594I85oMuBa40TuJSqAGUL4m4C+9kyigvwZO9E4i79QAyrcOPcLq4XTgG95J5J0aQHlmAl/zTqLAvoGtkizjpAZQnj/C5vYTHydh"
        "R2AyTmoA4zcL+Ip3EsLt6Chg3NQAxu9u4ATvJIQ64OveSeSVGsD4NKMRaVmyFjsdkIjUAMbny+gDlyXNwM3eSeRRLkZ9ZNAbwDne"
        "SSxdupS7776bZcuWMWHChJKvr6+v57TTThvzNTt27ODw4cMl/66jR4/S1tbGfffdx9atW0PnnKBXgCXeSUjluxT/8fDBypUrg56e"
        "npJj+5PW09MTrFy50n17DIQagCTufpw/6C0tLUF3d7d37X+mu7s7aGlp8S7+APirsvduwegaQDTVwA3eSaxYsYKmpibvND7T1NTE"
        "ihUrvNMAWIVOayNRA4jmEmDsk+gUTJuWvdveGclpFrDYO4k8UQOI5jrvBADeffdd7xSOk6GcMrGPpDK9iP95blBXVxds377d+9T/"
        "M9u3bw/q6urct8tAbCxzH4uMqBE4iv8HPACCJUuWBDt27PCu/WDHjh3BkiVL3LfHkDgC1JexnwtFF0zCuwr4gXcSQ02ePJnbbruN"
        "Cy+8MNQ4gKlTp7J8+fIxX7Nx40Z27txZ8u86evQoL7/8Mg8//DB79+4NnXNKvgi84J2EVJY/wP/bray4+uqrS36jX3XVVe55xhB3"
        "ldybAugiYBSt3glIaLoTEJIaQHjneicgoS3wTiAv1ADCqQLmeichoc3xTiAv1ADCmYImoMyTFuyujZSgBhCO++g/iWyGdwJ5oAYQ"
        "zineCUhkmV/hJAvUAMJp9k5AIpvknUAeqAGEo5l/80ejAUNQAwinxjuBOPT398fympyoiH2WNDWAcCqiKjo7O2N5TU5UxD5LmhpA"
        "OJ96JxCHt99+e8z5+9ra2rL0WG+5jngnIJXjGvzHt8cSra2twZ49e457BmD37t3BokWL3POLMcZ+6kkkgmX4f6Bji1mzZgUPPvhg"
        "0N7eHrS3twcPPPBAMHPmTPe8Yg4N3Q5BjwOHMwP4wDsJiWQKsNs7iaxTAwinGjgETPROREI5gIYCh6KLgOH0AxVzdawA3vZOIC/U"
        "AMJr905AQnvNO4G8UAMI76feCUhomVirLA/UAMLb5J2AhLbZO4G80EXA8OqAPWiMedbtA04Ger0TyQMdAYR3BHjeOwkp6TlU/KGp"
        "AUTzpHcCUtJT3gnkiU4BopmGDQjSk2bZ1IPN3rTHO5G80BFANB8B3/dOQkb1FCr+SNQAonvIOwEZ1T96J5A3OgWIrgYbaXaWdyJy"
        "jDewB4AC70TyREcA0fUB672TkOOsR8UfmY4AxucE4C3gDOc8xLwLLMRWb5YIdDV7fPqAXcAN3okIAGvR+H9JWRU2MMh74ouix7Ol"
        "dpRIUhYAh/EvgqLGAbRmY1l0ClCej7EGcI13IgX1dTQuQ5xVAf+F/7dh0eJRdBFbMqIZeBP/oihKvIqm/JKMmYMNFfYujkqPTmBW"
        "yH0iJegQKl7nY4+jnhz1Dy5dupQ5c+bEn1EGbdu2bcwFSsawE7gcG/UnkkmtwA5CfqPNnTs32LJly3ELdVS6LVu2BHPnzo3yzf8B"
        "dtdFJPPOxCYRHfND3djYGHR0dHjXopuOjo6gsbExTPH/DJiZ8j4sBD0LkIztwCXAY2O9aM2aNcyePTudjDJo9uzZrFmzptTLvgtc"
        "hp37S8zUAJKzH1iFDVPdP9ILLr300lQTyqIxtsEnwJeB1diAH0mAGkDyHsIeU31i+G/09PSkn03GjLIN/g17uOfhdLMpHjWAdHQC"
        "f8+wJauffVbD2EfYBgeB+4EP089GJBmXYYexx1zcqq2tDTZv3ux9Lc7N5s2bg9ra2pEu+u0DLnLaVyKxWoCtUjviFe6mpqZgw4YN"
        "QU9Pj3c9pqanpyfYsGFD0NTUNNaV/13APIf9VSgaCJSsKcAW7LbgmBoaGjjrrLOYOLGyFyA+cOAAnZ2dHDp0KMzL3wEuBvYmm5VI"
        "/GqwUYHeQ2fzHk+ja1WSQ9/Cv3gqJe6JuO1FXC3BFqnwLpxKiSPAeZH2gIiTGqAN/6KptNiETgUkB9bgXyyVGrdE2A8Sgu4CxKsO"
        "m6J6hnciFaoDmI+dXkkMdEgVr6+g4k/SGcCt3klUEh0BxKcKWyzkbO9EKlw7uiAYGx0BxOcKVPxpOBf4gncSlUINID43eSdQIKu9"
        "E6gUOgWIRzU2Ddip3okURBc2Q1DgnUje6QggHq2o+NM0A5svQMqkBhAPnZOm7zLvBCpBrXcCFeJ8gIULF7Jy5UpmzNCdwCR0dXXx"
        "2GOP8frrr8PANhfJgh+uW7cu6Ovr837UvuL19vYG9957bwD8j/dOFwHgpptu6vIujKJZvXr1e977vRLoGkD5GteuXTvVO4miueOO"
        "O6YDDd555J0aQPlunj9/vpZZT9m8efNq0XiAsqkBlO9Lu3bt8s6hcAa2+Ze888g7NYDyVAMXP/roo955FM7ANr8UDWYTRzOAoKGh"
        "odDTe6dt06ZNQX19/eAcARqAVQZ1z/IsBn4KUFdXxz333MOqVas0DiAhXV1dPPLII6xfv54jRz5bY+Vc4HXHtKTAluE/S07Ro7Xk"
        "XpJR6RpAeQ57JyDaB+VQAyjPR94JCDu9E8gzNYDy7MaWsRYfH6PtXxY1gPK95p1Agb3qnUDeqQGU7yXvBApM275MagDl+5F3AgWm"
        "bV8mjQMo34nYUtb13okUzEFs9eUjpV4oo9MRQPkOYivYSrq+h4pfMqIVOIT/oJiixCG0NoBkzK8AB/AvjkqP/cBVIfeJSKqWAu/h"
        "XySVGtvRXICScScDj+NfLJUWjwCTI+wHEVc3YgtYeBdO3qMTuCHithfJhBOBPwa68S+kvMVeYB2a908qwGTgW9jyYd6FlfXowgq/"
        "aVxbWiTDTgB+C/gB0Id/sWUlerF5/lcBE8a9dUVy5HTgLuAnFLMZ9ALPA78PTC9zW8o4aShwNpwKXAtcDVwJnOabTmI+BJ4DngWe"
        "wYZQiyM1gGyaj814ewk27dgi7PQhTz4Ffga0YU/tbQbeds1IjqMGkA8TgAXYktjnYg3iMmxW4izoxAr8LWyCznbgTeCoZ1JSmla0"
        "ybZq7Py4FTsKOA+bifgC7BpCVjQNRM1ATMSejuzFhkdLRukIIB3N2LZuxr7NG4FJA782AS3YCMKTganANOzbfTr5O/Qfrge7tdeF"
        "zaH4C2wqtd3Yvf5urEnsw8b592DTfAUDvycJKloDqMcKaypwClZ4zVgxnjjw60Rs8Ek9UDfw54YPQZ3E8UdPTRz7ePVg0Uv5+jl2"
        "7r/h/w12J2XfsP+3d+DXI9jswYcHft6HPca9b+A1e7D5BT/CGlVhHjOuxA9oFTAHWIIdMs8H5gKzsQkkRErZhT3UtQ27lvEatgDM"
        "Ns+kklAJDWA6VuwLgOXAF7BvdpG47QY2YbcynwQ6XLOJQR4bQBV2BfxGYAX2bS+StgD4MfAA8AR2CiIJqgPWYreZvEexKRRD4+fA"
        "75D/C7aZVA3cDnyA/45WKMaKDuBWNNdmbM4HXsZ/xyoUUaING8kp41QFfBMbTuq9MxWK8UQf8G3slrFEcBLw7/jvQIUijniPDE9i"
        "mrWhwNOwWyxXeCciEpMm4GZsYNlGbBBTZmTpNuBM4IfYoB2RSrQRu32dmSXNs9IApgL/C5ztnYhIwt4Dfo2MrGychdsVJwH/jYpf"
        "imE29mW33DsR8G8AVcB3sKG8IkXRhM2IdK13It4N4A+B33DOQcRDPTaE+BrPJDyvAVwMvADUOuYg4u0Q8MvY4KHUeTaATWi0lAjY"
        "dGqXefzDXg2gBXu0UkTMydjEJKnyugag5Z5EjuVSE14N4ENs+iXx1U/GRqYV1EdYTaTOqwH0A3/u9G8XXS82kcVd2D3pM4C7sVV6"
        "et2yKrY/w6kRe14ErMamVbreMYciOARsxS40PY8NR90/ymsnYVekl2MXaJeg07WkPQn8JvbgUOq8hwJPwsb/X+CcR94dwSZM6cJm"
        "p3kXW6TjtYGfxztdVQ02QvM8YB72nMaZ2HMbM/h81mQZn5ewJwUPeiXg3QDAptx+CpvMM0m/AN7n8+sPu7CrrvuxKaYPYnPSB5Se"
        "j76GY5/zbsCmEx/+80l8vtrt8KnEh75uuOE57MVW2TkwJN9u7E7KRxw/RXZamrHnOFqw/ThpIAbf99Cp0k9k9CmzDnDsKkKfYkcu"
        "w38+NPDfw38Os8/g830wYSDHJmxthhZsxujTBmL2wPtK0o+xb36tfYAVwt8Szyq5/diadA8AX8XW1mtM761IhWjEPjtrgAexz1Q/"
        "5X8++4D1aP7AEV0EfJ/oG/UodipxJ5W7sq74mw58Dfv27iX6F9PTwNK0kx5LFk4BRnIOcANwObYu3qlDfq8PO4x/C7u49QJ2ccvr"
        "MFiKqRm7YPpL2MXS+ViDGHpnbSfwCvAj4HHgnZRzLCmrDWC4Wj4/jO/G6YqpSAmD6z+CXavRbVURERERERERERERERERERERERER"
        "ERERERERERERERERERERERERERERERERERERERERERERERERERERkYrz/zyS+plAJfKKAAAAAElFTkSuQmCC"
    ),
    "r": (
        "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"
    ),
    "q": (
        "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"
        "pG9r4wAAAABJRU5ErkJggg=="
    ),
    "k": (
        "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"
        "RU5ErkJggg=="
    ),
}

def _decode_piece_images():
    """Decode the embedded base64 PNGs into PIL Images once, at import time."""
    if not PIECE_IMAGES_AVAILABLE:
        return {}
    images = {}
    for sym, b64 in PIECE_PNG_B64.items():
        try:
            raw = base64.b64decode(b64)
            images[sym] = Image.open(io.BytesIO(raw)).convert("RGBA")
        except Exception:
            pass
    return images


PIECE_PIL_IMAGES = _decode_piece_images()


CONFIG_PATH = os.path.join(os.path.expanduser("~"), ".chess_pgn_analyzer_config.json")


# ----------------------------
# Config persistence
# ----------------------------

def load_config():
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(data):
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f)
    except Exception:
        pass


# ----------------------------
# Analysis helpers
# ----------------------------

def score_to_cp(score, pov=chess.WHITE):
    """Return centipawn score from the requested POV."""
    s = score.pov(pov)
    if s.is_mate():
        return MATE_SCORE if s.mate() > 0 else -MATE_SCORE
    return s.score(mate_score=MATE_SCORE)


def format_score(cp):
    if abs(cp) >= MATE_SCORE:
        return "#+" if cp > 0 else "#-"
    return f"{cp / 100:+.2f}"


def classify(cpl):
    # Thresholds are deliberately conservative. They can be tuned.
    if cpl < 15:
        return "Excelente"
    if cpl < 40:
        return "Bom"
    if cpl < 80:
        return "Imprecisão"
    if cpl < 150:
        return "Erro"
    return "Blunder"


def win_probability(cp):
    """Converte a avaliação (POV Brancas) em probabilidade de vitória das Brancas (0.0 a 1.0)"""
    cp = max(-1000, min(1000, cp))
    return 0.5 + 0.5 * (2 / (1 + math.exp(-0.00368208 * cp)) - 1)


def calcular_precisao_moderna(eval_antes, eval_depois):
    """Calcula a precisão de um lance único baseado na queda de Win%"""
    win_antes = win_probability(eval_antes)
    win_depois = win_probability(eval_depois)

    perda_probabilidade = max(0, win_antes - win_depois) * 100
    precisao_lance = 103.1668 * math.exp(-0.04354 * perda_probabilidade) - 3.1669

    return max(0.0, min(100.0, precisao_lance))


def game_accuracy(resultados_analise, side):
    """Estimate game accuracy using volatility weighting and harmonic mean."""
    ordered = sorted(
        (r for r in resultados_analise if r["side"] in ("Brancas", "Pretas")),
        key=lambda r: r["ply"],
    )
    player_moves = [r for r in ordered if r["side"] == side]
    if not player_moves:
        return 100.0

    # Use consecutive engine evaluations to measure local position volatility.
    white_cps = [ordered[0]["eval_before_white"]]
    white_cps.extend(r["eval_after_white"] for r in ordered)
    win_percents = [win_probability(cp) * 100 for cp in white_cps]

    window_size = max(2, min(8, len(ordered) // 10))
    window_size = min(window_size, len(win_percents))
    windows = [win_percents[:window_size]] * max(0, window_size - 2)
    windows.extend(
        win_percents[i:i + window_size]
        for i in range(len(win_percents) - window_size + 1)
    )
    weights = [
        max(0.5, min(12.0, statistics.pstdev(window)))
        for window in windows
    ]

    weighted_moves = [
        (calcular_precisao_moderna(r["best"], r["played"]), weight)
        for r, weight in zip(ordered, weights)
        if r["side"] == side
    ]
    if not weighted_moves:
        return 100.0

    weighted_mean = sum(a * w for a, w in weighted_moves) / sum(
        w for _, w in weighted_moves
    )
    if any(a <= 0 for a, _ in weighted_moves):
        harmonic_mean = 0.0
    else:
        harmonic_mean = len(weighted_moves) / sum(
            1 / a for a, _ in weighted_moves
        )

    return max(0.0, min(100.0, (weighted_mean + harmonic_mean) / 2))


def parse_pgn(text):
    game = chess.pgn.read_game(io.StringIO(text))
    if game is None:
        raise ValueError("Não foi possível encontrar uma partida PGN válida.")
    if game.errors:
        raise ValueError("PGN contém erros: " + "; ".join(map(str, game.errors)))
    return game


def get_pv_text(board, pv, max_moves=8):
    b = board.copy()
    out = []
    for mv in pv[:max_moves]:
        if mv not in b.legal_moves:
            break
        out.append(b.san(mv))
        b.push(mv)
    return " ".join(out)


# ----------------------------
# Main application
# ----------------------------

class ChessAnalyzer(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Stockfish PGN Analyzer")
        self.geometry("1500x920")
        self.minsize(1150, 740)

        self.engine = None
        self._engine_path = None

        self.game = None
        self.moves = []
        self.positions = []
        self.results = []
        self.current_ply = 0
        self.analysis_running = False
        self._cancel_event = threading.Event()
        self._geom = None  # (x0, y0, sq) of the last board draw, for arrow placement
        self._piece_photo_cache = {}  # (symbol, px_bucket) -> ImageTk.PhotoImage

        self.stockfish_path = tk.StringVar()
        self.mode = tk.StringVar(value="depth")
        self.depth = tk.IntVar(value=18)
        self.time_sec = tk.DoubleVar(value=0.25)
        self.multipv = tk.IntVar(value=2)
        self.flipped = tk.BooleanVar(value=False)
        self.show_arrow = tk.BooleanVar(value=True)

        self._apply_saved_config()

        self._build_ui()
        self._load_default_pgn()
        self._bind_shortcuts()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------- Config ----------

    def _apply_saved_config(self):
        cfg = load_config()
        if not cfg:
            return
        self.stockfish_path.set(cfg.get("stockfish_path", self.stockfish_path.get()))
        self.mode.set(cfg.get("mode", self.mode.get()))
        self.depth.set(cfg.get("depth", self.depth.get()))
        self.time_sec.set(cfg.get("time_sec", self.time_sec.get()))
        self.multipv.set(cfg.get("multipv", self.multipv.get()))

    def _save_current_config(self):
        save_config({
            "stockfish_path": self.stockfish_path.get(),
            "mode": self.mode.get(),
            "depth": self.depth.get(),
            "time_sec": self.time_sec.get(),
            "multipv": self.multipv.get(),
        })

    # ---------- Shortcuts ----------

    def _bind_shortcuts(self):
        self.bind_all("<Left>", self._on_key_nav)
        self.bind_all("<Right>", self._on_key_nav)
        self.bind_all("<Home>", self._on_key_nav)
        self.bind_all("<End>", self._on_key_nav)

    def _on_key_nav(self, event):
        widget = self.focus_get()
        if isinstance(widget, (tk.Text, tk.Entry, ttk.Entry, ttk.Spinbox)):
            return
        if not self.positions:
            return
        if event.keysym == "Left":
            self.goto_ply(max(0, self.current_ply - 1))
        elif event.keysym == "Right":
            self.goto_ply(min(len(self.positions) - 1, self.current_ply + 1))
        elif event.keysym == "Home":
            self.goto_ply(0)
        elif event.keysym == "End":
            self.goto_ply(len(self.positions) - 1)

    # ---------- UI ----------

    def _build_ui(self):
        top = ttk.Frame(self, padding=8)
        top.pack(fill="x")

        ttk.Label(top, text="Stockfish:").pack(side="left")
        ttk.Entry(top, textvariable=self.stockfish_path, width=60).pack(side="left", padx=6)
        ttk.Button(top, text="Selecionar", command=self.choose_engine).pack(side="left")
        ttk.Button(top, text="Testar", command=self.test_engine).pack(side="left", padx=4)

        opts = ttk.LabelFrame(self, text="Configuração da análise", padding=8)
        opts.pack(fill="x", padx=8, pady=(0, 8))

        ttk.Radiobutton(opts, text="Profundidade", variable=self.mode,
                        value="depth").pack(side="left")
        ttk.Spinbox(opts, from_=8, to=40, textvariable=self.depth, width=6).pack(side="left", padx=5)

        ttk.Radiobutton(opts, text="Tempo por posição (s)", variable=self.mode,
                        value="time").pack(side="left", padx=(20, 0))
        ttk.Spinbox(opts, from_=0.05, to=10, increment=0.05,
                    textvariable=self.time_sec, width=7).pack(side="left", padx=5)

        ttk.Label(opts, text="MultiPV:").pack(side="left", padx=(20, 3))
        ttk.Spinbox(opts, from_=1, to=8, textvariable=self.multipv, width=5).pack(side="left")

        self.analyze_btn = ttk.Button(opts, text="ANALISAR PARTIDA", command=self.start_analysis)
        self.analyze_btn.pack(side="right")
        self.stop_btn = ttk.Button(opts, text="Parar", command=self.stop_analysis, state="disabled")
        self.stop_btn.pack(side="right", padx=(0, 6))

        paned = ttk.PanedWindow(self, orient="horizontal")
        paned.pack(fill="both", expand=True, padx=8, pady=4)

        left = ttk.Frame(paned)
        center = ttk.Frame(paned)
        right = ttk.Frame(paned)

        paned.add(left, weight=2)
        paned.add(center, weight=3)
        paned.add(right, weight=4)

        # PGN
        pgn_box = ttk.LabelFrame(left, text="PGN", padding=6)
        pgn_box.pack(fill="both", expand=True)

        self.pgn_text = tk.Text(pgn_box, wrap="word", font=("Consolas", 10))
        self.pgn_text.pack(fill="both", expand=True)

        pgn_buttons = ttk.Frame(pgn_box)
        pgn_buttons.pack(fill="x", pady=(6, 0))
        ttk.Button(pgn_buttons, text="Abrir PGN", command=self.open_pgn).pack(side="left")
        ttk.Button(pgn_buttons, text="Carregar", command=self.load_game_from_text).pack(side="left", padx=4)
        ttk.Button(pgn_buttons, text="Limpar", command=lambda: self.pgn_text.delete("1.0", "end")).pack(side="left", padx=4)
        ttk.Button(pgn_buttons, text="Exportar HTML", command=self.export_html).pack(side="left")
        ttk.Button(pgn_buttons, text="Exportar CSV", command=self.export_csv).pack(side="left", padx=4)

        # Board
        board_box = ttk.LabelFrame(center, text="Tabuleiro", padding=6)
        board_box.pack(fill="both", expand=True)

        board_row = ttk.Frame(board_box)
        board_row.pack(fill="both", expand=True)

        self.eval_bar_canvas = tk.Canvas(board_row, width=28, bg="#808080", highlightthickness=0)
        self.eval_bar_canvas.pack(side="left", fill="y", padx=(0, 6))
        self.eval_bar_canvas.bind("<Configure>", lambda e: self.draw_eval_bar())

        self.board_canvas = tk.Canvas(board_row, bg="#ddd", highlightthickness=0)
        self.board_canvas.pack(side="left", fill="both", expand=True)
        self.board_canvas.bind("<Configure>", lambda e: self.draw_board())

        nav = ttk.Frame(board_box)
        nav.pack(fill="x", pady=6)
        ttk.Button(nav, text="|<", command=lambda: self.goto_ply(0)).pack(side="left")
        ttk.Button(nav, text="<", command=lambda: self.goto_ply(max(0, self.current_ply - 1))).pack(side="left")
        ttk.Button(nav, text=">", command=lambda: self.goto_ply(min(len(self.positions) - 1, self.current_ply + 1))).pack(side="left")
        ttk.Button(nav, text=">|", command=lambda: self.goto_ply(max(0, len(self.positions) - 1))).pack(side="left")
        ttk.Button(nav, text="Girar tabuleiro", command=self.toggle_flip).pack(side="left", padx=(14, 0))
        ttk.Checkbutton(nav, text="Seta do melhor lance", variable=self.show_arrow,
                         command=self.draw_board).pack(side="left", padx=(14, 0))

        self.move_label = ttk.Label(nav, text="Nenhuma partida carregada")
        self.move_label.pack(side="left", padx=15)

        # Results
        result_box = ttk.LabelFrame(right, text="Análise", padding=6)
        result_box.pack(fill="both", expand=True)

        columns = ("ply", "move", "eval_before", "played", "best", "eval_after", "cpl", "class", "pv")
        self.tree = ttk.Treeview(result_box, columns=columns, show="headings", height=18)
        headers = {
            "ply": "#", "move": "Lance", "eval_before": "Antes",
            "played": "Jogado", "best": "Melhor", "eval_after": "Depois",
            "cpl": "CPL", "class": "Classificação", "pv": "PV"
        }
        widths = {"ply": 45, "move": 70, "eval_before": 65, "played": 65,
                  "best": 65, "eval_after": 65, "cpl": 55, "class": 100, "pv": 250}
        for c in columns:
            self.tree.heading(c, text=headers[c])
            self.tree.column(c, width=widths[c], anchor="center" if c != "pv" else "w")

        for cls, color in CLASS_COLORS.items():
            self.tree.tag_configure(cls, background=color)

        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.on_result_select)

        # Bottom
        bottom = ttk.Frame(self, padding=8)
        bottom.pack(fill="both")

        stats = ttk.LabelFrame(bottom, text="Resumo", padding=8)
        stats.pack(side="left", fill="x", expand=True)

        self.stats_label = ttk.Label(stats, text="Aguardando análise...")
        self.stats_label.pack(anchor="w")

        self.progress = ttk.Progressbar(bottom, mode="determinate", length=300)
        self.progress.pack(side="right", padx=8)

        self.status = ttk.Label(bottom, text="Pronto.")
        self.status.pack(side="right", padx=8)

        self._make_graph(bottom)

    def _make_graph(self, parent):
        graph_box = ttk.LabelFrame(parent, text="Avaliação", padding=4)
        graph_box.pack(side="left", fill="both", expand=True, padx=8)

        self.figure = Figure(figsize=(5, 2.2), dpi=90)
        self.ax = self.figure.add_subplot(111)
        self.ax.set_xlabel("Ply")
        self.ax.set_ylabel("Avaliação")
        self.ax.axhline(0, linewidth=0.8)
        self.figure.tight_layout()

        self.graph_canvas = FigureCanvasTkAgg(self.figure, master=graph_box)
        self.graph_canvas.draw()
        self.graph_canvas.get_tk_widget().pack(fill="both", expand=True)

    # ---------- Engine ----------

    def choose_engine(self):
        path = filedialog.askopenfilename(
            title="Selecione o executável do Stockfish",
            filetypes=[("Executável", "*.exe"), ("Todos os arquivos", "*.*")]
        )
        if path:
            self.stockfish_path.set(path)

    def ensure_engine(self):
        path = self.stockfish_path.get().strip()
        if not path or not os.path.exists(path):
            raise FileNotFoundError("Selecione o executável do Stockfish primeiro.")

        if self.engine is not None and self._engine_path == path:
            try:
                self.engine.ping()
                return
            except Exception:
                pass

        self._quit_engine()
        self.engine = chess.engine.SimpleEngine.popen_uci(path)
        self.engine.configure({
            "Threads": max(1, os.cpu_count() or 1),
            "Hash": min(1024, max(16, (os.cpu_count() or 2) * 64)),
        })
        self._engine_path = path

    def _quit_engine(self):
        if self.engine:
            try:
                self.engine.quit()
            except Exception:
                pass
        self.engine = None

    def test_engine(self):
        try:
            self.ensure_engine()
            info = self.engine.analyse(chess.Board(), chess.engine.Limit(depth=10))
            self.status.config(text="Stockfish OK — " + format_score(score_to_cp(info["score"])))
        except Exception as e:
            messagebox.showerror("Stockfish", str(e))

    def on_close(self):
        self._save_current_config()
        self._cancel_event.set()
        self._quit_engine()
        self.destroy()

    # ---------- PGN ----------

    def open_pgn(self):
        path = filedialog.askopenfilename(filetypes=[("PGN", "*.pgn"), ("Todos", "*.*")])
        if not path:
            return
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
        self.pgn_text.delete("1.0", "end")
        self.pgn_text.insert("1.0", text)

    def _load_default_pgn(self):
        sample = """[Event "Exemplo"]
[Site "?"]
[Date "2026.01.01"]
[Round "1"]
[White "White"]
[Black "Black"]
[Result "*"]

1. e4 e5 2. Nf3 Nc6 3. Bb5 a6 4. Ba4 Nf6 5. O-O Be7 *"""
        self.pgn_text.insert("1.0", sample)

    def load_game_from_text(self):
        if self.analysis_running:
            messagebox.showinfo("Análise em andamento", "Aguarde a análise atual terminar ou pare-a antes de carregar outra partida.")
            return None

        try:
            game = parse_pgn(self.pgn_text.get("1.0", "end"))
        except Exception as e:
            messagebox.showerror("PGN inválido", str(e))
            return None

        self.game = game
        self.moves = list(game.mainline_moves())

        board = game.board()
        positions = [board.copy()]
        for mv in self.moves:
            board.push(mv)
            positions.append(board.copy())
        self.positions = positions

        self.results.clear()
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.ax.clear()
        self.ax.axhline(0, linewidth=0.8)
        self.graph_canvas.draw()
        self.stats_label.config(text="Aguardando análise...")
        self.progress["value"] = 0

        self.current_ply = 0
        self.draw_board()
        self.draw_eval_bar()
        self.move_label.config(text=f"Ply 0/{len(self.positions) - 1}")
        self.status.config(text=f"Partida carregada: {len(self.moves)} lances.")
        return game

    # ---------- Analysis ----------

    def _current_limit(self):
        if self.mode.get() == "depth":
            return chess.engine.Limit(depth=int(self.depth.get()))
        return chess.engine.Limit(time=float(self.time_sec.get()))

    def _analyse(self, board, limit, mpv):
        infos = self.engine.analyse(board, limit, multipv=mpv)
        return infos[0] if isinstance(infos, list) else infos

    def start_analysis(self):
        if self.analysis_running:
            return

        game = self.load_game_from_text()
        if game is None:
            return
        if not self.moves:
            messagebox.showinfo("Análise", "A partida não contém lances.")
            return

        try:
            self.ensure_engine()
        except Exception as e:
            messagebox.showerror("Stockfish", str(e))
            return

        self._cancel_event.clear()
        self.analysis_running = True
        self.analyze_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.progress["value"] = 0
        self.progress["maximum"] = max(1, len(self.moves))
        self.status.config(text="Analisando...")
        threading.Thread(target=self._analysis_worker, daemon=True).start()

    def stop_analysis(self):
        self._cancel_event.set()
        self.status.config(text="Interrompendo...")

    def _analysis_worker(self):
        limit = self._current_limit()
        mpv = max(1, int(self.multipv.get()))

        try:
            prev_info = self._analyse(self.positions[0], limit, mpv)
        except Exception as e:
            self.after(0, lambda: self._analysis_error(str(e)))
            return

        try:
            for i, move in enumerate(self.moves):
                if self._cancel_event.is_set():
                    break

                board = self.positions[i]
                next_board = self.positions[i + 1]
                side = board.turn

                best_cp = score_to_cp(prev_info["score"], side)
                best_cp_white = score_to_cp(prev_info["score"], chess.WHITE)
                best_pv = prev_info.get("pv", [])
                best_move = best_pv[0] if best_pv else None

                next_info = self._analyse(next_board, limit, mpv)
                played_cp = score_to_cp(next_info["score"], side)
                played_cp_white = score_to_cp(next_info["score"], chess.WHITE)
                cpl = max(0, best_cp - played_cp)

                result = {
                    "ply": i + 1,
                    "move": board.san(move),
                    "side": "Brancas" if side == chess.WHITE else "Pretas",
                    "eval_before": best_cp,
                    "played": played_cp,
                    "best": best_cp,
                    "eval_after": played_cp,
                    "eval_before_white": best_cp_white,
                    "eval_after_white": played_cp_white,
                    "best_move": best_move,
                    "cpl": cpl,
                    "class": classify(cpl),
                    "pv": get_pv_text(board, best_pv),
                }
                self.results.append(result)

                self.after(0, lambda r=result: self.add_result(r))
                self.after(0, lambda x=i + 1: self.progress.configure(value=x))
                self.after(0, self.draw_eval_bar)

                prev_info = next_info

        except chess.engine.EngineTerminatedError as e:
            self.after(0, lambda: self._analysis_error(f"O motor foi encerrado inesperadamente: {e}"))
            return
        except Exception as e:
            self.after(0, lambda: self._analysis_error(str(e)))
            return

        self.after(0, self.analysis_finished)

    def _analysis_error(self, msg):
        self.analysis_running = False
        self.analyze_btn.config(state="normal")
        self.stop_btn.config(state="disabled")
        self.status.config(text="Erro na análise.")
        messagebox.showerror("Erro na análise", msg)

    def add_result(self, r):
        self.tree.insert(
            "", "end",
            iid=str(r["ply"]),
            values=(
                r["ply"],
                r["move"],
                format_score(r["eval_before"]),
                format_score(r["played"]),
                format_score(r["best"]),
                format_score(r["eval_after"]),
                r["cpl"],
                r["class"],
                r["pv"]
            ),
            tags=(r["class"],)
        )

    def analysis_finished(self):
        self.analysis_running = False
        self.analyze_btn.config(state="normal")
        self.stop_btn.config(state="disabled")

        white = [r for r in self.results if r["side"] == "Brancas"]
        black = [r for r in self.results if r["side"] == "Pretas"]

        avg_cpl_white = sum(r["cpl"] for r in white) / len(white) if white else 0
        avg_cpl_black = sum(r["cpl"] for r in black) / len(black) if black else 0

        self.stats_label.config(
            text=(
                f"Precisão aproximada — Brancas: {game_accuracy(self.results, 'Brancas'):.1f}% | "
                f"Pretas: {game_accuracy(self.results, 'Pretas'):.1f}%     "
                f"CPL médio — Brancas: {avg_cpl_white:.1f} | "
                f"Pretas: {avg_cpl_black:.1f}"
            )
        )

        finished_all = len(self.results) == len(self.moves)
        if finished_all:
            self.status.config(text=f"Concluído: {len(self.results)} lances analisados.")
        else:
            self.status.config(text=f"Interrompido: {len(self.results)}/{len(self.moves)} lances analisados.")

        self.update_graph()
        self.draw_eval_bar()

    # ---------- Board ----------

    def toggle_flip(self):
        self.flipped.set(not self.flipped.get())
        self.draw_board()
        self.draw_eval_bar()

    def goto_ply(self, ply):
        if not self.positions:
            return
        self.current_ply = max(0, min(ply, len(self.positions) - 1))
        self.draw_board()
        self.draw_eval_bar()

        if 0 < self.current_ply <= len(self.results):
            iid = str(self.current_ply)
            if self.tree.selection() != (iid,):
                self.tree.selection_set(iid)
            self.tree.see(iid)
        else:
            current = self.tree.selection()
            if current:
                self.tree.selection_remove(*current)

        self.move_label.config(text=f"Ply {self.current_ply}/{len(self.positions) - 1}")

    def on_result_select(self, _event):
        selected = self.tree.selection()
        if selected:
            ply = int(selected[0])
            if ply != self.current_ply:
                self.goto_ply(ply)

    def _square_at(self, row, col, flipped):
        """Map a displayed (row, col) grid cell — row 0 = top — to a chess square."""
        if flipped:
            r = row
            f = 7 - col
        else:
            r = 7 - row
            f = col
        return chess.square(f, r)

    def _display_rc(self, square, flipped):
        """Map a chess square to displayed (row, col) — row 0 = top."""
        f = chess.square_file(square)
        r = chess.square_rank(square)
        if flipped:
            return r, 7 - f
        return 7 - r, f

    def _get_piece_photo(self, piece, px):
        """Return a cached, correctly-sized PhotoImage for this piece, or None
        if Pillow / the embedded artwork isn't available (caller should then
        fall back to the text renderer)."""
        if not PIECE_IMAGES_AVAILABLE:
            return None
        sym = PIECE_KEY[(piece.piece_type, piece.color)]
        base_img = PIECE_PIL_IMAGES.get(sym)
        if base_img is None:
            return None

        px_bucket = max(8, (px // 4) * 4)
        key = (sym, px_bucket)
        photo = self._piece_photo_cache.get(key)
        if photo is not None:
            return photo

        if len(self._piece_photo_cache) > 400:
            self._piece_photo_cache.clear()

        resample = getattr(getattr(Image, "Resampling", Image), "LANCZOS")
        resized = base_img.resize((px_bucket, px_bucket), resample)
        photo = ImageTk.PhotoImage(resized)
        self._piece_photo_cache[key] = photo
        return photo

    def _draw_piece(self, cx, cy, sq, piece):
        """Draw a piece using the bundled solid, minimalist artwork, falling
        back to a text glyph if Pillow / the artwork is unavailable."""
        px = max(8, int(sq * 0.88))
        photo = self._get_piece_photo(piece, px)
        if photo is not None:
            self.board_canvas.create_image(cx, cy, image=photo)
        else:
            self._draw_piece_text(cx, cy, sq, piece)

    def _draw_piece_text(self, cx, cy, sq, piece):
        """Fallback renderer: a flat, solid, high-contrast text glyph, used
        only when Pillow isn't installed."""
        symbol = PIECE_SYMBOLS[(piece.piece_type, piece.color)]
        font = ("DejaVu Sans", int(sq * 0.74), "bold")
        if piece.color == chess.WHITE:
            fill, outline = "#ffffff", "#1a1a1a"
        else:
            fill, outline = "#1a1a1a", "#ffffff"

        offset = max(1, sq * 0.025)
        for dx, dy in ((-offset, 0), (offset, 0), (0, -offset), (0, offset)):
            self.board_canvas.create_text(cx + dx, cy + dy, text=symbol, font=font, fill=outline)
        self.board_canvas.create_text(cx, cy, text=symbol, font=font, fill=fill)

    def _draw_arrow(self, from_sq, to_sq, x0, y0, sq, flipped, color="#1e6fd9"):
        fr, fc = self._display_rc(from_sq, flipped)
        tr, tc = self._display_rc(to_sq, flipped)
        fx, fy = x0 + fc * sq + sq / 2, y0 + fr * sq + sq / 2
        tx, ty = x0 + tc * sq + sq / 2, y0 + tr * sq + sq / 2
        self.board_canvas.create_line(
            fx, fy, tx, ty,
            fill=color, width=max(4, int(sq * 0.11)),
            arrow=tk.LAST, arrowshape=(sq * 0.32, sq * 0.4, sq * 0.16),
            capstyle=tk.ROUND, joinstyle=tk.ROUND
        )

    def draw_board(self):
        if not self.positions:
            return

        self.board_canvas.delete("all")
        w = self.board_canvas.winfo_width()
        h = self.board_canvas.winfo_height()
        size = min(w, h)
        if size <= 20:
            return

        x0 = (w - size) / 2
        y0 = (h - size) / 2
        sq = size / 8
        self._geom = (x0, y0, sq)
        flipped = self.flipped.get()

        board = self.positions[self.current_ply]
        light = "#f0d9b5"
        dark = "#b58863"
        light_hl = "#f6f669"
        dark_hl = "#cdd26a"

        last_move = None
        if 0 < self.current_ply <= len(self.moves):
            last_move = self.moves[self.current_ply - 1]
        highlighted = {last_move.from_square, last_move.to_square} if last_move else set()

        # Squares
        for row in range(8):
            for col in range(8):
                x = x0 + col * sq
                y = y0 + row * sq
                square = self._square_at(row, col, flipped)
                # a1 is a dark square: (file + rank) even => dark, odd => light.
                is_light = (chess.square_rank(square) + chess.square_file(square)) % 2 == 1

                if square in highlighted:
                    fill = light_hl if is_light else dark_hl
                else:
                    fill = light if is_light else dark

                self.board_canvas.create_rectangle(x, y, x + sq, y + sq, fill=fill, outline="")

        # Best-move arrow (drawn under the pieces)
        if self.show_arrow.get() and self.current_ply < len(self.results):
            best_move = self.results[self.current_ply].get("best_move")
            if best_move is not None:
                self._draw_arrow(best_move.from_square, best_move.to_square, x0, y0, sq, flipped)

        # Pieces
        for row in range(8):
            for col in range(8):
                square = self._square_at(row, col, flipped)
                piece = board.piece_at(square)
                if piece:
                    cx = x0 + col * sq + sq / 2
                    cy = y0 + row * sq + sq / 2
                    self._draw_piece(cx, cy, sq, piece)

        # Coordinates
        files = "abcdefgh" if not flipped else "hgfedcba"
        ranks = "87654321" if not flipped else "12345678"
        for i in range(8):
            self.board_canvas.create_text(
                x0 + i * sq + 4, y0 + 8 * sq - 10,
                text=files[i], anchor="sw",
                font=("Arial", max(7, int(sq * 0.13)))
            )
            self.board_canvas.create_text(
                x0 + 4, y0 + i * sq + 4,
                text=ranks[i], anchor="nw",
                font=("Arial", max(7, int(sq * 0.13)))
            )

    # ---------- Evaluation bar ----------

    def _current_eval_white(self):
        """Centipawn evaluation (White POV) of the position at the current ply,
        or None if that position hasn't been analysed yet."""
        if self.current_ply == 0:
            if self.results:
                return self.results[0]["eval_before_white"]
            return None
        idx = self.current_ply - 1
        if idx < len(self.results):
            return self.results[idx]["eval_after_white"]
        return None

    def draw_eval_bar(self):
        self.eval_bar_canvas.delete("all")
        w = self.eval_bar_canvas.winfo_width()
        h = self.eval_bar_canvas.winfo_height()
        if w <= 4 or h <= 4:
            return

        cp_white = self._current_eval_white()

        if cp_white is None:
            self.eval_bar_canvas.create_rectangle(0, 0, w, h, fill="#909090", outline="")
            self.eval_bar_canvas.create_line(0, h / 2, w, h / 2, fill="#ffffff")
            return

        wp = win_probability(cp_white)
        flipped = self.flipped.get()

        white_h = h * wp
        if not flipped:
            # White at the bottom of the board -> white share at the bottom of the bar
            self.eval_bar_canvas.create_rectangle(0, 0, w, h - white_h, fill="#202020", outline="")
            self.eval_bar_canvas.create_rectangle(0, h - white_h, w, h, fill="#f5f5f5", outline="")
            label_y = 10 if wp < 0.5 else h - 10
            label_fill = "#f5f5f5" if wp < 0.5 else "#202020"
        else:
            black_h = h * (1 - wp)
            self.eval_bar_canvas.create_rectangle(0, 0, w, h - black_h, fill="#f5f5f5", outline="")
            self.eval_bar_canvas.create_rectangle(0, h - black_h, w, h, fill="#202020", outline="")
            label_y = 10 if wp >= 0.5 else h - 10
            label_fill = "#f5f5f5" if wp >= 0.5 else "#202020"

        self.eval_bar_canvas.create_line(0, h / 2, w, h / 2, fill="#888888")

        if abs(cp_white) >= MATE_SCORE:
            label = "#+" if cp_white > 0 else "#-"
        else:
            label = format_score(cp_white)
        self.eval_bar_canvas.create_text(
            w / 2, label_y, text=label, font=("Arial", 8, "bold"), fill=label_fill
        )

    # ---------- Graph ----------

    def update_graph(self):
        self.ax.clear()
        if not self.results:
            self.ax.axhline(0, linewidth=0.8)
            self.graph_canvas.draw()
            return

        cap = 12  # cap for display so mate scores don't blow out the scale
        x = [r["ply"] for r in self.results]
        y = [max(-cap, min(cap, r["eval_after_white"] / 100)) for r in self.results]

        self.ax.plot(x, y, linewidth=1.2, color="#333333")
        self.ax.fill_between(x, y, 0, where=[v >= 0 for v in y], color="#e6e6e6", interpolate=True)
        self.ax.fill_between(x, y, 0, where=[v < 0 for v in y], color="#4d4d4d", interpolate=True)
        self.ax.axhline(0, linewidth=0.8, color="#888888")
        self.ax.set_ylim(-cap, cap)
        self.ax.set_xlabel("Ply")
        self.ax.set_ylabel("Avaliação (Brancas)")
        self.ax.set_title("Evolução da avaliação")
        self.figure.tight_layout()
        self.graph_canvas.draw()

    # ---------- Export ----------

    def export_html(self):
        if not self.results:
            messagebox.showinfo("Exportar", "Analise uma partida primeiro.")
            return

        path = filedialog.asksaveasfilename(
            defaultextension=".html",
            filetypes=[("HTML", "*.html")]
        )
        if not path:
            return

        rows = []
        for r in self.results:
            rows.append(
                "<tr>" +
                "".join(f"<td>{r[k]}</td>" for k in
                        ["ply", "move", "eval_before", "best", "eval_after", "cpl", "class", "pv"]) +
                "</tr>"
            )

        html = f"""<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<title>Stockfish PGN Analysis</title>
<style>
body {{ font-family: Arial; margin: 30px; }}
table {{ border-collapse: collapse; width: 100%; }}
th, td {{ border: 1px solid #ccc; padding: 6px; }}
th {{ background: #eee; }}
</style>
</head>
<body>
<h1>Stockfish PGN Analysis</h1>
<p>{self.stats_label.cget("text")}</p>
<table>
<thead><tr>
<th>Ply</th><th>Lance</th><th>Antes</th><th>Melhor</th>
<th>Depois</th><th>CPL</th><th>Classificação</th><th>PV</th>
</tr></thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
</body>
</html>"""

        with open(path, "w", encoding="utf-8") as f:
            f.write(html)

        messagebox.showinfo("Exportar", "Relatório HTML salvo com sucesso.")

    def export_csv(self):
        if not self.results:
            messagebox.showinfo("Exportar", "Analise uma partida primeiro.")
            return

        path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv")]
        )
        if not path:
            return

        fieldnames = ["ply", "move", "side", "eval_before", "played", "best",
                      "eval_after", "eval_before_white", "eval_after_white",
                      "cpl", "class", "pv"]
        with open(path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            for r in self.results:
                writer.writerow(r)

        messagebox.showinfo("Exportar", "CSV exportado com sucesso.")


if __name__ == "__main__":
    app = ChessAnalyzer()
    app.mainloop()
