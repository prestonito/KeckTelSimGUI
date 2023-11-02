## TelSIM GUI Documentation

#### Author: Preston Ito

##### bash example
this is a simple bash example 
```bash
python3 -m mkdocs serve
```

##### python example
this is a simple python example
```python
>>> import subsystem
```

##### Imports and KPython Address
These are all the imports necessary for the code. It also has KPython address and sets up EPICS channels for translation stage simulators. A good chunk of this code comes from another GUI project created by Paul Richards. His source code was used as a template for this GUI.
```python
#! @KPYTHON3@
#
# kpython safely sets RELDIR, KROOT, LROOT, and PYTHONPATH before invoking
# the actual Python interpreter.

# Setup an EPICS address list if one is not already defined

import os
import subprocess
import datetime
import time

addrs = 'localhost:5064 vm-k1epicsgateway:5064 vm-k2epicsgateway:5064 k1aoserver-new:8607 localhost:5555'

print(f'Overriding EPICS address list to: {addrs}')
os.environ['EPICS_CA_ADDR_LIST'] = addrs
os.environ['EPICS_CA_AUTO_ADDR_LIST'] = 'NO'

# Keck library includes
import ktl  # provided by kroot/ktl/keyword/python
import kPyQt  # provided by kroot/kui/kPyQt

import logging, coloredlogs
import argparse
import sys
import datetime
import base64
from dateutil.parser import isoparse
import requests
import io
from enum import Enum, auto
import urllib
import functools

from PyQt5 import QtCore, QtWidgets, uic
from PyQt5.QtWidgets import QStatusBar, QMessageBox, QWidget, QVBoxLayout, QLabel, QPushButton, \
    QToolButton, QSpacerItem, QSizePolicy, QFileDialog, QShortcut, QLCDNumber, QLayout
from PyQt5.QtCore import Qt, QSize, QTimer
from PyQt5.QtGui import QFont, QIcon, QPixmap, QImage, QIntValidator, QDoubleValidator, QKeySequence
from PyQt5.Qt import QApplication

from PToggle import PToggle, PAnimatedToggle

from datetime import datetime
```


##### Constants, showDialog function, and state machine class
These are all of the constants used throughout the code. A showDialog function is included to be called whenever QMessageBoxes are used. The code was structured using state machines.
```python

debug = False

SECONDS = 1
FONTBOLD = 'Montserrat SemiBold'
FONTLIGHT = 'Montserrat Light'
STATUSBAR_WHITE_STYLE = 'QStatusBar{padding-left:8px;background:white;color:black;font-weight:bold;}'
STATUSBAR_YELLOW_STYLE = 'QStatusBar{padding-left:8px;background:yellow;color:black;font-weight:bold;}'
EDIT_STYLE = 'font: 25 14pt "Montserrat SemiBold";'
MODE_CLEAR_STYLE = 'background-color: rgb(255, 255, 255);'
MODE_SET_STYLE = 'background-color: rgb(0, 170, 0);'
MODE_UNSET_STYLE = 'background-color: rgb(170, 170, 170);'

STATUS_RED_STYLE = 'background-color: rgb(255, 0, 0);'
STATUS_GREEN_STYLE = 'background-color: rgb(0, 255, 0);'
MESSAGE_LIMIT = 100


class TelSimStates(Enum):
    OFF = 0
    ON = auto()
    IDLE = auto()
    MOVE_ALT = auto()
    AWAIT_ALT = auto()
    MOVE_WIND = auto()
    AWAIT_WIND = auto()
    STOPPED = auto()
    CLEANUP = auto()


def showDialog(text, yes=False, cancel=False):
    '''
    Show a message box to the user.

    :param text: The message to be displayed.
    :param yes: Use "Yes/No" instead of "OK/Cancel"
    :param cancel: Show a Cancel button, versus just OK.
    :return: Nothing.
    '''

    # Create a message box
    msgBox = QtWidgets.QMessageBox()
    msgBox.setIcon(QMessageBox.Information)
    msgBox.setText(text)
    msgBox.setWindowTitle('Message')

    # Add buttons, either OK or OK+Cancel or Yes+No
    if yes:
        msgBox.setStandardButtons(QMessageBox.Yes | QMessageBox.No)
    elif cancel:
        msgBox.setStandardButtons(QMessageBox.Ok | QMessageBox.Cancel)
    else:
        msgBox.setStandardButtons(QMessageBox.Ok)

    # Test the return from the message box
    returnValue = msgBox.exec()
    if returnValue in [QMessageBox.Ok, QMessageBox.Yes]:
        return True
    else:
        return False
```