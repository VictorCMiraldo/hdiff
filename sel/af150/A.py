"""deCONZ climate platform tests."""
from copy import deepcopy
from unittest.mock import Mock, patch

import asynctest

from homeassistant import config_entries
from homeassistant.components import deconz
from homeassistant.helpers.dispatcher import async_dispatcher_send
from homeassistant.setup import async_setup_component

import homeassistant.components.climate as climate

from tests.common import mock_coro


SENSOR = {
    "1": {
        "id": "Climate 1 id",
        "name": "Climate 1 name",
        "type": "ZHAThermostat",
        "state": {"on": True, "temperature": 2260, "valve": 30},
        "config": {
            "battery": 100,
            "heatsetpoint": 2200,
            "mode": "auto",
            "offset": 10,
            "reachable": True,
        },
        "uniqueid": "00:00:00:00:00:00:00:00-00",
    },
    "2": {
        "id": "Sensor 2 id",
        "name": "Sensor 2 name",
        "type": "ZHAPresence",
        "state": {"presence": False},
        "config": {},
    },
}

ENTRY_CONFIG = {
    deconz.config_flow.CONF_API_KEY: "ABCDEF",
    deconz.config_flow.CONF_BRIDGEID: "0123456789",
    deconz.config_flow.CONF_HOST: "1.2.3.4",
    deconz.config_flow.CONF_PORT: 80,
}

ENTRY_OPTIONS = {
    deconz.const.CONF_ALLOW_CLIP_SENSOR: True,
    deconz.const.CONF_ALLOW_DECONZ_GROUPS: True,
}


async def setup_gateway(hass, data, allow_clip_sensor=True):
    """Load the deCONZ sensor platform."""
    from pydeconz import DeconzSession

    response = Mock(
        status=200, json=asynctest.CoroutineMock(), text=asynctest.CoroutineMock()
    )
    response.content_type = "application/json"

    session = Mock(put=asynctest.CoroutineMock(return_value=response))

    ENTRY_OPTIONS[deconz.const.CONF_ALLOW_CLIP_SENSOR] = allow_clip_sensor

    config_entry = config_entries.ConfigEntry(
        1,
        deconz.DOMAIN,
        "Mock Title",
        ENTRY_CONFIG,
        "test",
        config_entries.CONN_CLASS_LOCAL_PUSH,
        system_options={},
        options=ENTRY_OPTIONS,
    )
    gateway = deconz.DeconzGateway(hass, config_entry)
    gateway.api = DeconzSession(hass.loop, session, **config_entry.data)
    gateway.api.config = Mock()
    hass.data[deconz.DOMAIN] = {gateway.bridgeid: gateway}

    with patch("pydeconz.DeconzSession.async_get_state", return_value=mock_coro(data)):
        await gateway.api.async_load_parameters()

    await hass.config_entries.async_forward_entry_setup(config_entry, "climate")
    # To flush out the service call to update the group
    await hass.async_block_till_done()
    return gateway


async def test_platform_manually_configured(hass):
    """Test that we do not discover anything or try to set up a gateway."""
    assert (
        await async_setup_component(
            hass, climate.DOMAIN, {"climate": {"platform": deconz.DOMAIN}}
        )
        is True
    )
    assert deconz.DOMAIN not in hass.data


async def test_no_sensors(hass):
    """Test that no sensors in deconz results in no climate entities."""
    gateway = await setup_gateway(hass, {})
    assert not hass.data[deconz.DOMAIN][gateway.bridgeid].deconz_ids
    assert not hass.states.async_all()


async def test_climate_devices(hass):
    """Test successful creation of sensor entities."""
    gateway = await setup_gateway(hass, {"sensors": deepcopy(SENSOR)})
    assert "climate.climate_1_name" in gateway.deconz_ids
    assert "sensor.sensor_2_name" not in gateway.deconz_ids
    assert len(hass.states.async_all()) == 1

    gateway.api.sensors["1"].async_update({"state": {"on": False}})

    await hass.services.async_call(
        "climate",
        "set_hvac_mode",
        {"entity_id": "climate.climate_1_name", "hvac_mode": "heat"},
        blocking=True,
    )
    gateway.api.session.put.assert_called_with(
        "http://1.2.3.4:80/api/ABCDEF/sensors/1/config", data='{"mode": "auto"}'
    )

    await hass.services.async_call(
        "climate",
        "set_hvac_mode",
        {"entity_id": "climate.climate_1_name", "hvac_mode": "off"},
        blocking=True,
    )
    gateway.api.session.put.assert_called_with(
        "http://1.2.3.4:80/api/ABCDEF/sensors/1/config", data='{"mode": "off"}'
    )

    await hass.services.async_call(
        "climate",
        "set_temperature",
        {"entity_id": "climate.climate_1_name", "temperature": 20},
        blocking=True,
    )
    gateway.api.session.put.assert_called_with(
        "http://1.2.3.4:80/api/ABCDEF/sensors/1/config", data='{"heatsetpoint": 2000.0}'
    )

    assert len(gateway.api.session.put.mock_calls) == 3


async def test_verify_state_update(hass):
    """Test that state update properly."""
    gateway = await setup_gateway(hass, {"sensors": deepcopy(SENSOR)})
    assert "climate.climate_1_name" in gateway.deconz_ids

    thermostat = hass.states.get("climate.climate_1_name")
    assert thermostat.state == "off"

    state_update = {
        "t": "event",
        "e": "changed",
        "r": "sensors",
        "id": "1",
        "state": {"on": False},
    }
    gateway.api.async_event_handler(state_update)

    await hass.async_block_till_done()
    assert len(hass.states.async_all()) == 1

    thermostat = hass.states.get("climate.climate_1_name")
    assert thermostat.state == "off"
    assert gateway.api.sensors["1"].changed_keys == {"state", "r", "t", "on", "e", "id"}


async def test_add_new_climate_device(hass):
    """Test successful creation of climate entities."""
    gateway = await setup_gateway(hass, {})
    sensor = Mock()
    sensor.name = "name"
    sensor.type = "ZHAThermostat"
    sensor.uniqueid = "1"
    sensor.register_async_callback = Mock()
    async_dispatcher_send(hass, gateway.async_event_new_device("sensor"), [sensor])
    await hass.async_block_till_done()
    assert "climate.name" in gateway.deconz_ids


async def test_do_not_allow_clipsensor(hass):
    """Test that clip sensors can be ignored."""
    gateway = await setup_gateway(hass, {}, allow_clip_sensor=False)
    sensor = Mock()
    sensor.name = "name"
    sensor.type = "CLIPThermostat"
    sensor.register_async_callback = Mock()
    async_dispatcher_send(hass, gateway.async_event_new_device("sensor"), [sensor])
    await hass.async_block_till_done()
    assert len(gateway.deconz_ids) == 0


async def test_unload_sensor(hass):
    """Test that it works to unload sensor entities."""
    gateway = await setup_gateway(hass, {"sensors": SENSOR})

    await gateway.async_reset()

    assert len(hass.states.async_all()) == 0
