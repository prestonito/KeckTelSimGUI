#! @KPYTHON3@
#
# kpython safely sets RELDIR, KROOT, LROOT, and PYTHONPATH before invoking
# the actual Python interpreter.

import os

# Setup an EPICS address list if one is not already defined
addrs = 'localhost:5064 vm-k1epicsgateway:5064 vm-k2epicsgateway:5064 k1aoserver-new:8607 localhost:5555 localhost:5556 k1aoserver-new:5064'



# addrs = 'localhost:5064 vm-k1epicsgateway:5064 vm-k2epicsgateway:5064 k1aoserver-new:5064 localhost:5555 localhost:5556'

print(f'Overriding EPICS address list to: {addrs}')
os.environ['EPICS_CA_ADDR_LIST'] = addrs
os.environ['EPICS_CA_AUTO_ADDR_LIST'] = 'NO'

# Keck library includes
import ktl  # provided by kroot/ktl/keyword/python
import kPyQt  # provided by kroot/kui/kPyQt

import logging, coloredlogs
import argparse
import sys
import base64
from dateutil.parser import isoparse
import requests
import io
from enum import Enum, auto
import urllib
import functools
import subprocess
import time
import math

from PyQt5 import QtCore, QtWidgets, uic
from PyQt5.QtWidgets import QStatusBar, QMessageBox, QWidget, QVBoxLayout, QLabel, QPushButton, \
    QToolButton, QSpacerItem, QSizePolicy, QFileDialog, QShortcut, QLCDNumber, QLayout
from PyQt5.QtCore import Qt, QSize, QTimer
from PyQt5.QtGui import QFont, QIcon, QPixmap, QImage, QIntValidator, QDoubleValidator, QKeySequence
from PyQt5.Qt import QApplication

from PToggle import PToggle, PAnimatedToggle

debug = False

SECONDS = 1
UNBINNED_MODE = 2000
BINNED_MODE = 3600
WIND_POS_HOME = 0.00
VEL_HOME = 2.00
ACCEL_HOME = 0.10
ALT_POS_HOME = 5.0
STOP = "0"
MOVE = "3"
WIND_POS_MIN = -40.00
WIND_POS_MAX = 40.00
VEL_MIN = 2.00
VEL_MAX = 80.00
ACCEL_MIN = 0.00
ACCEL_MAX = 10.00
ALT_MIN = 5.0
ALT_MAX = 12.0
GAIN_MIN = 0
GAIN_MAX = 1
FRAMERATE_MIN = 1
TIMEOUT_MS = 45000
STATUS_RED_STYLE = 'background-color: rgb(255, 0, 0);'
# STATUS_GREEN_STYLE = 'background-color: rgb(0, 255, 0);'
MESSAGE_LIMIT = 100


class TelSimStates(Enum):
    INIT = 0
    OFF = auto()
    IDLE = auto()
    MOVE_ALT = auto()
    AWAIT_ALT = auto()
    MOVE_WIND = auto()
    AWAIT_WIND = auto()
    STOPPED = auto()
    CLEANUP = auto()
    AWAIT_CLEANUP = auto()


def showDialog(text, yes=False, cancel=False):
    '''
    Show a message box to the user.

    :param text: The message to be displayed.
    :param yes: Use "Yes/No" instead of "OK/Cancel"
    :param cancel: Show a Cancel button, versus just OK.
    :return: True if 'Ok' or 'Yes' is pressed, False if not.
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


class TurbulenceSimulatorGUIMain(QtWidgets.QMainWindow):

    # -----------------------------------------------------------------------------
    def __init__(self, *args, **kwargs):

        # self.list = None
        self.popups = {}
        self.template = None

        # Make access to data be thread safe with a mutex (chart data, in particular)
        self._mutex = QtCore.QMutex()

        QtWidgets.QMainWindow.__init__(self, *args, **kwargs)

        # Load the UI file
        uifile = 'telsim.ui'
        path = '.'
        filename = os.path.join(path, uifile)

        if not os.path.exists(filename):
            filename = os.path.join(os.environ['KROOT'], 'rel/ao/default/data', uifile)

        uic.loadUi(filename, self)

    # -----------------------------------------------------------------------------
    def setupUI(self, channels=None):

        title = 'Telescope Simulator GUI'
        self.setWindowTitle(title)

        # -----------------------------------------------------------------------------
        # Make the menu bar work the same across all platforms (looking at you, MacOS)
        self.menubar.setNativeMenuBar(False)

        # Timers
        self.countdownTimer = QTimer()  # Display timer
        self.countdownTimer.setSingleShot(True)
        self.LCDnumbers.display("0.00")
        self.secondsToMove = 0

        # Enabling/disabling feature when TelSIM button pressed
        self.controls = [self.windTSBox, self.TSBox, self.altGroupBox, self.wavefrontGroupBox, self.fileGroupBox,
                         self.loopocBox, self.loopControlLabel]

        # Actions! Connects buttons/text fields to functions
        self.selectFileButton.clicked.connect(self.fileSelection)
        self.reconstructorButton.clicked.connect(self.reconstructorSelection)
        self.openLoop.clicked.connect(self.openLoopButton_clicked)
        self.closedLoop.clicked.connect(self.closeLoopButton_clicked)
        self.bin.toggled.connect(lambda: self.frameRateCheck(self.frameRateInput.text()))
        self.unbin.toggled.connect(lambda: self.frameRateCheck(self.frameRateInput.text()))

        # Creates 'changed' attributes for the background color feature while editing
        setattr(self.posBox, 'changed', False)
        self.posBox.editingFinished.connect(lambda: self.posCheck(self.posBox.text()))
        self.posBox.textChanged.connect(lambda: self.editTextChanged(self.posBox))

        setattr(self.velBox, 'changed', False)
        self.velBox.editingFinished.connect(lambda: self.velCheck(self.velBox.text()))
        self.velBox.textChanged.connect(lambda: self.editTextChanged(self.velBox))

        setattr(self.accelBox, 'changed', False)
        self.accelBox.editingFinished.connect(lambda: self.accelCheck(self.accelBox.text()))
        self.accelBox.textChanged.connect(lambda: self.editTextChanged(self.accelBox))

        setattr(self.altBox, 'changed', False)
        self.altBox.editingFinished.connect(lambda: self.altCheck(self.altBox.text()))
        self.altBox.textChanged.connect(lambda: self.editTextChanged(self.altBox))

        setattr(self.gainInput, 'changed', False)
        self.gainInput.editingFinished.connect(lambda: self.gainCheck(self.gainInput.text()))
        self.gainInput.textChanged.connect(lambda: self.editTextChanged(self.gainInput))

        setattr(self.frameRateInput, 'changed', False)
        self.frameRateInput.editingFinished.connect(lambda: self.frameRateCheck(self.frameRateInput.text()))
        self.frameRateInput.textChanged.connect(lambda: self.editTextChanged(self.frameRateInput))

        # Channel creation for the emulator
        self.posChan = kPyQt.caFactory("wndsim:ln:m1.RBV", kPyQt.Channel.caFloat)
        self.posWritingChan = kPyQt.caFactory("wndsim:ln:m1.VAL", kPyQt.Channel.caFloat)
        self.posMovingChan = kPyQt.caFactory("wndsim:ln:m1.MOVN", kPyQt.Channel.caFloat)
        self.velChan = kPyQt.caFactory("wndsim:ln:m1.VELO", kPyQt.Channel.caFloat)
        self.accelChan = kPyQt.caFactory("wndsim:ln:m1.ACCL", kPyQt.Channel.caFloat)
        self.altChan = kPyQt.caFactory("altsim:ln:m1.RBV", kPyQt.Channel.caFloat)
        self.altWritingChan = kPyQt.caFactory("altsim:ln:m1.VAL", kPyQt.Channel.caFloat)
        self.altMovingChan = kPyQt.caFactory("altsim:ln:m1.MOVN", kPyQt.Channel.caFloat)
        self.windStopChan = kPyQt.caFactory("wndsim:ln:m1.SPMG", kPyQt.Channel.caFloat)
        self.altStopChan = kPyQt.caFactory("altsim:ln:m1.SPMG", kPyQt.Channel.caFloat)

        # Other GUI connections dropdown
        self.oth1.triggered.connect(self.openOther)
        self.oth2.triggered.connect(self.openOther)
        self.oth3.triggered.connect(self.openOther)

        # --------- Reading telemetry example -----------------------------------------
        service = 'ao1'
        ao1 = ktl.cache(service)
        # -----------------------------------------------------------------------------------------
        # A label attached to an KTL string keyword
        dt_key = 'dtlp'
        self.dt_keyword = kPyQt.kFactory(ao1[dt_key])

        dm_key = 'dmlp'
        self.dm_keyword = kPyQt.kFactory(ao1[dm_key])

        fr_key = 'wsfrrt'  # Alternate keyword for frame rate for now (framerate keyword is not configured for the new RTC). Actual keyword is o1fps
        self.frameRate_keyword = kPyQt.kFactory(ao1[fr_key])

        gain_key = 'dtgain'  # Fake keyword for gain for now (gain keyword is not configured for the new RTC). Actual keyword is o1wgs
        self.gain_keyword = kPyQt.caFactory('k1:ao:wc:dt:sv:gain', kPyQt.Channel.caFloat)

        # -----------------------------------------------------------------------------------

        # ------ Translation stages' toggles --------------------------------------------
        self.TS1 = PToggle(handle_color=Qt.red, checked_color=Qt.green)
        TS1lay = QVBoxLayout()
        TS1lay.addWidget(self.TS1)
        self.TS1tog.setLayout(TS1lay)
        self.TS1.setCheckState(Qt.Unchecked)

        self.TS2 = PToggle(handle_color=Qt.red, checked_color=Qt.green)
        TS2lay = QVBoxLayout()
        TS2lay.addWidget(self.TS2)
        self.TS2tog.setLayout(TS2lay)
        self.TS2.setCheckState(Qt.Unchecked)
        # --------------------------------------------------------------------

        # State machine support
        self.setupTelSIMButtonWasPressed = False
        self.setupTelSIMButton.clicked.connect(self.setupTelSIMButtonPressed)
        self.closeTelSIMButtonWasPressed = False
        self.closeTelSIMButton.clicked.connect(self.closeTelSIMButtonPressed)
        self.startButtonWasPressed = False
        self.startButton.clicked.connect(self.startButtonPressed)
        self.stopButtonWasPressed = False
        self.stopButton.clicked.connect(self.stopButtonPressed)
        self.stateTimeout = QTimer()
        self.stateTimeout.setSingleShot(True)
        self.stateMachineTimer = QTimer()
        self.stateMachineTimer.timeout.connect(self.stateMachine)
        self.stateMachineTimer.start(75)
        self.state = TelSimStates.INIT

    def setupTelSIMButtonPressed(self):
        """
        Trigger the state machine with a button press.
        """
        self.setupTelSIMButtonWasPressed = True

    def closeTelSIMButtonPressed(self):
        """
        Closes the state machine with a button press.
        """
        self.closeTelSIMButtonWasPressed = True

    def startButtonPressed(self):
        """
        Trigger MOVE_ALT stage with a button press.
        """
        self.startButtonWasPressed = True

    def stopButtonPressed(self):
        """
        Trigger MOVE_ALT stage with a button press.
        """
        self.stopButtonWasPressed = True

    def stateMachine(self):
        """
        State machine processing.
        """
        self.statusbar.showMessage(f'STATE: {self.state.name}')

        # ----- STATE 0 ------------------------------------------------
        if self.state == TelSimStates.INIT:
            # Connects to the channels to read and display the values
            self.posChan.floatCallback.connect(self.posBoxSetText)
            self.posChan.runCallbacks()
            self.velChan.floatCallback.connect(self.velBoxSetText)
            self.velChan.runCallbacks()
            self.accelChan.floatCallback.connect(self.accelBoxSetText)
            self.accelChan.runCallbacks()
            self.altChan.floatCallback.connect(self.altBoxSetText)
            self.altChan.runCallbacks()

            self.dt_keyword.stringCallback.connect(self.loopController)
            self.dt_keyword.primeCallback()

            self.dm_keyword.stringCallback.connect(self.loopController)
            self.dm_keyword.primeCallback()

            self.frameRate_keyword.stringCallback.connect(self.frBoxSetText)
            self.frameRate_keyword.primeCallback()

            self.gain_keyword.floatCallback.connect(self.gainBoxSetText)
            self.gain_keyword.runCallbacks()

            self.state = TelSimStates.OFF
            return

        # ----- STATE 1 ------------------------------------------------
        elif self.state == TelSimStates.OFF:

            # Update GUI widgets for the OFF state
            self.startButton.setVisible(True)
            self.startButton.setEnabled(False)
            self.stopButton.setVisible(False)

            self.setupTelSIMButton.setEnabled(True)
            self.setupTelSIMButton.setVisible(True)

            self.closeTelSIMButton.setEnabled(False)
            self.closeTelSIMButton.setVisible(False)

            for i in self.controls:
                i.setEnabled(False)  # Disable the widgets

            # If setup is pressed, advance to IDLE
            if self.setupTelSIMButtonWasPressed:
                self.setupTelSIMButtonWasPressed = False

                # Advance the state machine
                self.state = TelSimStates.IDLE
                return

            return

        # ----- STATE 2 -----------------------------------------
        elif self.state == TelSimStates.IDLE:

            # Update GUI widgets visibility
            self.startstopBox.setEnabled(True)
            self.startButton.setVisible(True)
            self.startButton.setEnabled(True)
            self.stopButton.setVisible(False)
            self.stopButton.setEnabled(False)
            self.setupTelSIMButton.setEnabled(False)
            self.setupTelSIMButton.setVisible(False)
            self.closeTelSIMButton.setEnabled(True)
            self.closeTelSIMButton.setVisible(True)
            self.LCDnumbers.display("0.00")

            for i in self.controls:
                i.setEnabled(True)  # Enable the widgets

            if self.startButtonWasPressed:
                self.startButtonWasPressed = False
                self.state = TelSimStates.MOVE_ALT
                return

            if self.closeTelSIMButtonWasPressed:
                self.closeTelSIMButtonWasPressed = False
                self.state = TelSimStates.CLEANUP
                return

            return

        # ----- STATE 3 -----------------------------------------
        elif self.state == TelSimStates.MOVE_ALT:
            self.finalPos = self.posBox.text()
            self.finalAlt = self.altBox.text()

            self.initialPos = float(self.posChan.read())
            self.secondsToMove = abs(float(self.initialPos) - float(self.finalPos)) / float(
                self.velBox.text())  # Note: self.velBox.text() is only assigned after being validated
            self.LCDnumbers.display(f"{self.secondsToMove:0.2f}")
            self.initialAlt = float(self.altChan.read())
            if showDialog("Are you sure you want to START?", yes=True, cancel=True):
                for i in self.controls:
                    i.setEnabled(False)  # Disable the widgets
                self.startButton.setVisible(False)
                self.startButton.setEnabled(False)
                self.stopButton.setVisible(True)
                self.stopButton.setEnabled(True)
                self.altStopChan.write(MOVE)
                self.altWrite(self.altBox.text())
                self.altBox.changed = False
                self.stateTimeout.start(TIMEOUT_MS)
                self.state = TelSimStates.AWAIT_ALT
                return
            else:
                self.state = TelSimStates.IDLE
                return


        # ----- STATE 4 -----------------------------------------
        elif self.state == TelSimStates.AWAIT_ALT:
            if math.isclose(float(self.altChan.read()), float(self.finalAlt), abs_tol=0.05):
                self.stateTimeout.stop()
                self.stateTimeout.start(TIMEOUT_MS)
                self.state = TelSimStates.MOVE_WIND
                return
            if self.stopButtonWasPressed:
                self.stateTimeout.stop()
                self.stopButtonWasPressed = False
                self.state = TelSimStates.STOPPED
                return

            if not self.stateTimeout.isActive():
                raise TimeoutError("Alt TS took more than 45 seconds to move")
                return
            return

        # ----- STATE 5 -----------------------------------------
        elif self.state == TelSimStates.MOVE_WIND:
            self.posBox.changed = False
            self.velBox.changed = False
            self.accelBox.changed = False
            self.windStopChan.write(MOVE)
            self.accelWrite(self.accelBox.text())
            self.velWrite(self.velBox.text())
            self.posWrite(self.posBox.text())
            self.countdownTimer.start(int(self.secondsToMove) * 1000)
            self.stateTimeout.start(TIMEOUT_MS)
            self.state = TelSimStates.AWAIT_WIND
            return

        # ----- STATE 6 -----------------------------------------
        elif self.state == TelSimStates.AWAIT_WIND:
            self.timeLeft = self.countdownTimer.remainingTime() / 1000
            self.LCDnumbers.display(f"{self.timeLeft:0.2f}")
            if math.isclose(float(self.posChan.read()), float(self.finalPos), abs_tol=0.05):
                self.stateTimeout.stop()
                self.state = TelSimStates.IDLE
                return
            if self.stopButtonWasPressed:
                self.stopButtonWasPressed = False
                self.stateTimeout.stop()
                self.state = TelSimStates.STOPPED
                return
            if not self.stateTimeout.isActive():
                raise TimeoutError("Wind TS took more than 45 seconds to move")
                return

            return

        # ----- STATE 7 -----------------------------------------
        elif self.state == TelSimStates.STOPPED:
            self.windStopChan.write(STOP)
            self.altStopChan.write(STOP)
            self.countdownTimer.stop()
            self.state = TelSimStates.IDLE
            return

        # ----- STATE 8 -----------------------------------------
        elif self.state == TelSimStates.CLEANUP:
            self.closeTelSIMButton.setVisible(False)
            self.closeTelSIMButton.setEnabled(False)
            self.setupTelSIMButton.setVisible(True)
            self.setupTelSIMButton.setEnabled(False)
            self.startstopBox.setEnabled(False)
            for i in self.controls:
                i.setEnabled(False)
            self.windStopChan.write(MOVE)
            self.altStopChan.write(MOVE)
            self.posWrite(WIND_POS_HOME)
            self.velWrite(VEL_HOME)
            self.accelWrite(ACCEL_HOME)
            self.altWrite(ALT_POS_HOME)
            time.sleep(2)
            self.stateTimeout.start(TIMEOUT_MS)
            self.state = TelSimStates.AWAIT_CLEANUP
            return

        # ----- STATE 9 -----------------------------------------
        elif self.state == TelSimStates.AWAIT_CLEANUP:
            if int(self.altMovingChan.read()) == 0:
                if int(self.posMovingChan.read()) == 0:
                    if math.isclose(float(self.accelChan.read()), 0.2, abs_tol=0.2):
                        if math.isclose(float(self.velChan.read()), 2.1, abs_tol=0.2):
                            self.state = TelSimStates.OFF
                            return

            if not self.stateTimeout.isActive():
                raise TimeoutError("Cleanup took more than 45 seconds")
                return
            return

    # -----------------------------------------------------------------------------
    def editTextChanged(self, edit):
        '''Qt signal that something was typed in the edit field'''
        edit.changed = True
        edit.setStyleSheet('background-color: red')

    # -----------------------------------------------------------------------------
    def editReturnPressed(self, channel, edit):
        '''Qt signal that enter or return was pressed in the edit, pass the event as if the Set button was clicked'''
        self.setChannel(channel, edit)

    # -----------------------------------------------------------------------------
    def editFinished(self, edit):
        '''Qt signal that the edit field lost focus when editing, revert the value'''
        if edit.changed:
            edit.setText(edit.undoText)
            edit.changed = False
            edit.setStyleSheet(self.editStyleSheet)

    def openOther(self):
        '''Open external GUIs'''
        subprocess.call(['ssh', 'k1obsao@k1aoserver-new', '/kroot/rel/ao/qfix/setup_ao.csh'])

    def posBoxSetText(self, val):
        if not self.posBox.changed:
            self.posBox.setStyleSheet("")
            self.posBox.blockSignals(True)  # Turn off signals to the edit, a human is not editing it!
            self.posBox.setText(f"{val:0.2f}")
            self.posBox.blockSignals(False)  # Turn on signals to the edit, a human is not editing it!

    def velBoxSetText(self, val):
        if not self.velBox.changed:
            self.velBox.setStyleSheet("")
            self.velBox.blockSignals(True)  # Turn off signals to the edit, a human is not editing it!
            self.velBox.setText(f"{val:0.2f}")
            self.velBox.blockSignals(False)  # Turn on signals to the edit, a human is not editing it!

    def accelBoxSetText(self, val):
        if not self.accelBox.changed:
            self.accelBox.setStyleSheet("")
            self.accelBox.blockSignals(True)  # Turn off signals to the edit, a human is not editing it!
            self.accelBox.setText(f"{val:0.2f}")
            self.accelBox.blockSignals(False)  # Turn on signals to the edit, a human is not editing it!

    def altBoxSetText(self, val):
        if not self.altBox.changed:
            self.altBox.setStyleSheet("")
            self.altBox.blockSignals(True)  # Turn off signals to the edit, a human is not editing it!
            self.altBox.setText(f"{val:0.1f}")
            self.altBox.blockSignals(False)  # Turn on signals to the edit, a human is not editing it!

    def frBoxSetText(self, val):
        if not self.frameRateInput.changed:
            self.frameRateInput.setStyleSheet("")
            self.frameRateInput.blockSignals(True)  # Turn off signals to the edit, a human is not editing it!
            self.frameRateInput.setText(f"{val}")
            self.frameRateInput.blockSignals(False)  # Turn on signals to the edit, a human is not editing it!

    def gainBoxSetText(self, val):
        if not self.gainInput.changed:
            self.gainInput.setStyleSheet("")
            self.gainInput.blockSignals(True)  # Turn off signals to the edit, a human is not editing it!
            self.gainInput.setText(f"{val:0.2f}")
            self.gainInput.blockSignals(False)  # Turn on signals to the edit, a human is not editing it!

    # ---- Select file buttons -----------------------------------------------
    def fileSelection(self):
        fname = QFileDialog.getOpenFileName(self, 'Open File', '~', 'TXT files (*.txt)')
        self.fileImportTxt.setText(fname[0])

    def reconstructorSelection(self):
        fname = QFileDialog.getOpenFileName(self, 'Open File', '~', 'TXT files (*.txt)')
        self.recon.setText(fname[0])

    # -----------------------------------------------------------------------

    # --- Corrects pos/vel/accel/alt values after edited? --------------------
    def posCheck(self, msg):
        '''
        Makes sure the value entered in the field is within bounds. If not, will show error message. Also assigns
        self.finalPos used later for calculating time it will take to move
        :param msg: Value entered in posBox text box
        '''
        self.posBox.validator = QDoubleValidator(WIND_POS_MIN, WIND_POS_MAX, 2,
                                                 notation=QDoubleValidator.StandardNotation)
        if QDoubleValidator.validate(self.posBox.validator, str(msg), 0)[
            0] != 2:  # When this object is != 2, that means that it's not an acceptable input
            self.posBox.setText(f"{float(self.posChan.read()):0.2f}")
            showDialog("Position must be a float between -40.00 and 40.00")

    def velCheck(self, msg):
        self.velBox.validator = QDoubleValidator(VEL_MIN, VEL_MAX, 2, notation=QDoubleValidator.StandardNotation)
        if QDoubleValidator.validate(self.velBox.validator, str(msg), 0)[0] != 2:
            self.velBox.setText(f"{float(self.velChan.read()):0.2f}")
            showDialog("Velocity must be a float between 2.00 and 80.00")
        else:
            # Ensures self.velVal assignment ONLY if the input passes the validator
            self.velVal = msg

    def accelCheck(self, msg):
        self.accelBox.validator = QDoubleValidator(ACCEL_MIN, ACCEL_MAX, 2, notation=QDoubleValidator.StandardNotation)
        if QDoubleValidator.validate(self.accelBox.validator, str(msg), 0)[0] != 2:
            self.accelBox.setText(f"{float(self.accelChan.read()):0.2f}")
            showDialog("Acceleration must be a float between 0.00 and 10.00")

    def gainCheck(self, msg):
        self.gainInput.validator = QDoubleValidator(GAIN_MIN, GAIN_MAX, 2, notation=QDoubleValidator.StandardNotation)
        if QDoubleValidator.validate(self.gainInput.validator, str(msg), 0)[0] != 2:
            self.gainInput.setText(f"{float(self.gain_keyword.read()):0.2f}")
            showDialog("Gain must be between 0 and 1")
        else:
            self.gain_keyword.write(msg)
        self.gainInput.changed = False

    def altCheck(self, msg):
        self.altBox.validator = QDoubleValidator(ALT_MIN, ALT_MAX, 1, notation=QDoubleValidator.StandardNotation)
        if QDoubleValidator.validate(self.altBox.validator, str(msg), 0)[0] != 2:
            self.altBox.setText(f"{float(self.altChan.read()):0.1f}")
            showDialog("Altitude must be between 5.0 and 12.0")

    def frameRateCheck(self, msg):
        if self.unbin.isChecked() == True:
            self.frameRateInput.validator = QIntValidator(FRAMERATE_MIN, UNBINNED_MODE, self)
        else:
            self.frameRateInput.validator = QIntValidator(FRAMERATE_MIN, BINNED_MODE, self)
        if QIntValidator.validate(self.frameRateInput.validator, str(msg), 0)[0] != 2:
            self.frameRateInput.setText("1")
            showDialog("Frame rate must be integer between 1-2000 when in unbinned mode and "
                       "1-3600 when in binned mode; automatically reset frame to 1")
        else:
            self.frameRate_keyword.write(msg)
        self.frameRateInput.changed = False

    # ---------------------------------------------------------------------

    # ---- Writes the pos/vel/accel/alt to the emulator --------------------------------------------
    def posWrite(self, msg):
        '''
        Writes the value to the writing channel

        :param msg: Position value
        '''
        f = float(msg)
        self.posWritingChan.write(f, wait=False)

    def velWrite(self, msg):
        f = float(msg)
        self.velChan.write(f)

    def accelWrite(self, msg):
        f = float(msg)
        self.accelChan.write(f)

    def altWrite(self, msg):
        f = float(msg)
        self.altWritingChan.write(f, wait=False)

    # -------------------------------------------------------------------------

    def loopController(self):
        """
        Selects the correct radio button based on status of dmlp and dtlp keywords
        """
        if self.dt_keyword.read() == "CLOSE" and self.dm_keyword.read() == "CLOSE":
            self.closedLoop.setChecked(True)
        else:
            self.openLoop.setChecked(True)

    def openLoopButton_clicked(self):
        """
        Turns loop off (opens loop)
        """
        if self.dt_keyword.read() == "CLOSE" or self.dm_keyword.read() == "CLOSE":
            self.dm_keyword.write("OPEN")
            time.sleep(0.5)
            self.dt_keyword.write("OPEN")

    def closeLoopButton_clicked(self):
        """
        Turns loop on (closes loop)
        """
        if self.dt_keyword.read() == "OPEN" or self.dm_keyword.read() == "OPEN":
            self.dt_keyword.write("CLOSE")
            time.sleep(0.5)
            self.dm_keyword.write("CLOSE")


if __name__ == '__main__':

    # -------------------------------------------------------------------------
    # Commandline arguments
    parser = argparse.ArgumentParser(description='Turbulence Simulator GUI')
    parser.add_argument('-d', '--debug', help='Enable debugging output', action='store_true')
    args = parser.parse_args()

    # Get the debug argument first, as it drives our logging choices
    if args.debug:
        debug = True

    # -------------------------------------------------------------------------
    # Set up the base logger all threads will use, once we know the debug flag
    coloredlogs.DEFAULT_LOG_FORMAT = '%(asctime)s [%(levelname)s] %(message)s'
    coloredlogs.DEFAULT_DATE_FORMAT = '%Y-%m-%d %H:%M:%S.%f'
    if debug:
        coloredlogs.install(level='DEBUG')
    else:
        coloredlogs.install(level='INFO')
    log = logging.getLogger('')

    # Disable the debug logging from Qt
    logging.getLogger('PyQt5').setLevel(logging.WARNING)

    application = QtWidgets.QApplication(sys.argv)
    mainwin = TurbulenceSimulatorGUIMain()
    mainwin.setupUI()
    # mainwin.setMinimumSize(0, 0)
    # mainwin.resize(10,10)
    mainwin.show()

    # Run the Qt application
    status = kPyQt.run(application)
    sys.exit(status)

