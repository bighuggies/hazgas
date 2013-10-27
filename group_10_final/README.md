# Hazardous Gas

## Prerequisites

 * Spin 6.2
   http://spinroot.com/spin/Man/README.html

 * Git

 * Make

## Verification
 1. Clone the repo

        git clone https://github.com/bighuggies/hazgas.git

 2. View claims

        cat claims.ltl

 3. Compile the source code and run the verifier

        make

## Simulation

Installation Instructions for HazGas Simulator:
1.	Download and install unity.
2.	Create a new project
3.	Copy the assets folder contained within the Simulation directory & paste it in the root directory of the new project.
4.	Run Unity
5.	Open the BasicScene scene.
6.	Run the project with the play button at the top of the screen.

Move around the scene with the WSAD keys.
Hold down the right mouse button to change the view
Click with the left mouse button and drag over an area to create a new room.

Located in the top left corner of the screen are a number of button and sliders.
The top slider indicates the alarm threshold. A threshold of 10% indicates that the alarm will trigger if any rooms have been venting for 10% of the recorded history. Sliding the slider to the left indicates a threshold of 0%, sliding to the right indicates a threshold of 100%.
The middle slider shows the percentage of the past 800 frames in which rooms have been venting.
The last slider indicates the rate at which gas accumulates. Moving the slider to the left indicates a fill rate of 0 litres per second, and moving the slider to the right indicates a fill rate of 20 litres. 