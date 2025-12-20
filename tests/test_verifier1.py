import pytest
from .conftest import *


class TestVerifier:
    """Test the TaskNet verifier on valid task networks"""

    def test_tasknet1_1(self):
        """Finds a valid schedule, properties hold"""
        verify_out('tasknet1.tn')(
            "*** NEW SCHEDULE***",
            "heating       : start =    1, end =   81",
            "driving       : start =  100, end =  180",
            "communicating : start =  200, end =  280",
            "PROPERTY 'p1' HOLDS",
            "PROPERTY 'p2' HOLDS",
            "PROPERTY 'p3' HOLDS",
        )

    def test_tasknet2(self):
        """
        Modifiation of tasknet1:
        Loosening start and end ranges, finds diffeerent schedule, p2 violated
        """
        verify_out('tasknet2.tn')(
            "heating       : start =   82, end =  162",
            "driving       : start =  163, end =  243",
            "communicating : start =    1, end =   81",
            "PROPERTY 'p1' HOLDS",
            "PROPERTY 'p2' VIOLATED!",    
            "PROPERTY 'p3' HOLDS"
        )

    def test_tasknet3(self):
        """
        Modification of tasknet2:
        Adds property as a constraint. Now all properties hold again.
        """
        verify_out('tasknet3.tn')(
            "heating       : start =    1, end =   81",
            "driving       : start =   82, end =  162",
            "communicating : start =  163, end =  243",
            "PROPERTY 'p1' HOLDS",
            "PROPERTY 'p2' HOLDS",
            "PROPERTY 'p3' HOLDS"
        )

    def test_tasknet4_containedin(self):
        """Simplest possible test."""
        verify_out('tasknet4_containedin.tn')(
            "parent_task   : start =    2, end =  102",
            "child_task    : start =    3, end =   43",
            "No temporal properties attached to this TaskNet."
        )

    def test_tasknet5_containedin(self):
        """..."""
        verify_out('tasknet5_containedin.tn')(
            "power_session : start =    2, end =  102",
            "sensor_reading: start =    3, end =   43",
            "No temporal properties attached to this TaskNet."
        )
